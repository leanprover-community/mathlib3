-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.basic
import data.list.defs

/-
A basic `library_search` tactic.
-/

namespace tactic
open native

namespace library_search

meta def head_symbol : expr → name
| (expr.pi _ _ _ t) := head_symbol t
| (expr.app f _) := head_symbol f
| (expr.const n _) :=
  -- TODO this is a hack; if you suspect more cases here would help, please report them
  match n with
  | `gt := `has_lt.lt
  | `ge := `has_le.le
  | _   := n
  end
| _ := `_

inductive head_symbol_match
| ex | mp | mpr | both

open head_symbol_match

def head_symbol_match.to_string : head_symbol_match → string
| ex   := "exact"
| mp   := "iff.mp"
| mpr  := "iff.mpr"
| both := "iff.mp and iff.mpr"

meta def unfold_head_symbol : name → list name
| `false := [`not, `false]
| n      := [n]

meta def match_head_symbol (hs : name) : expr → option head_symbol_match
| (expr.pi _ _ _ t) := match_head_symbol t
| `(%%a ↔ %%b)      := if `iff = hs then some ex else
                       match (match_head_symbol a, match_head_symbol b) with
                       | (some ex, some ex) :=
                           some both
                       | (some ex, _) := some mpr
                       | (_, some ex) := some mp
                       | _ := none
                       end
| (expr.app f _)    := match_head_symbol f
| (expr.const n _)  := if list.mem hs (unfold_head_symbol n) then some ex else none
| _ := none

meta structure decl_data :=
(d : declaration)
(n : name)
(m : head_symbol_match)
(l : ℕ) -- cached length of name

-- We used to check here for private declarations, or declarations with certain suffixes.
-- It turns out `apply` is so fast, it's better to just try them all.
meta def process_declaration (hs : name) (d : declaration) : option decl_data :=
let n := d.to_name in
if ¬ d.is_trusted ∨ n.is_internal then
  none
else
  (λ m, ⟨d, n, m, n.length⟩) <$> match_head_symbol hs d.type

/-- Retrieve all library definitions with a given head symbol. -/
meta def library_defs (hs : name) : tactic (list decl_data) :=
do env ← get_env,
   return $ env.decl_filter_map (process_declaration hs)

meta def apply_and_solve (e : expr) :=
apply e >>
(done <|>
 solve_by_elim
 { all_goals := tt })

-- meta def update_univ (p : list (level × level)) (l : level) : level :=
-- ((p.find (λ q : level × level, q.1 = l)).map prod.snd).get_or_else l

-- meta def update_univs (p : list (level × level)) : expr → expr
-- | (expr.var n)        := expr.var n
-- | (expr.sort l)       := expr.sort (update_univ p l)
-- | (expr.const n ls)   := expr.const n (ls.map (update_univ p))
-- | (expr.mvar n m e)   := expr.mvar n m (update_univs e)
-- | (expr.local_const n m bi e) := expr.local_const n m bi (update_univs e)
-- | (expr.app f x)      := expr.app (update_univs f) (update_univs x)
-- | (expr.lam n bi d t) := expr.lam n bi (update_univs d) (update_univs t)
-- | (expr.pi n bi d t)  := expr.pi n bi (update_univs d) (update_univs t)
-- | (expr.elet n a b c) := expr.elet n (update_univs a) (update_univs b) (update_univs c)
-- | (expr.macro d es)   := expr.macro d (es.map update_univs)

-- /--
-- Returns a pair (e, t), where `e ← mk_const d.n`, and `t = d.type`,
-- but with universe params updated to match the fresh universe metavariables in `e`.

-- This is ever so slightly faster than just using `t ← infer_type e`.
-- -/
-- meta def decl_mk_const (d : declaration) : tactic (expr × expr) :=
-- do let old := d.univ_params.map level.param,
--    e ← mk_const d.to_name,
--    new ← match e with
--    | (expr.const _ l) := some l
--    | _ := none
--    end,
--    trace old,
--    trace new,
--    return (e, update_univs (old.zip new) d.type)

meta def apply_declaration (d : decl_data) : tactic unit :=
do
   /- `decl_mk_const` should be slightly fast than calling `infer_type`,
      however I just can't get it to work. The relevant test case is in
      test/library_search/ordered_ring.lean -/
   -- (e, t) ← decl_mk_const d.d,

   e ← mk_const d.n,
   t ← infer_type e,
   match d.m with
   | ex := apply_and_solve e
   | mp :=
      do l ← iff_mp_core e t,
         apply_and_solve l
   | mpr :=
      do l ← iff_mpr_core e t,
         apply_and_solve l
   | both :=
      (do l ← iff_mp_core e t,
         apply_and_solve l) <|>
      (do l ← iff_mpr_core e t,
         apply_and_solve l)
   end

end library_search

open library_search
open library_search.head_symbol_match

declare_trace silence_library_search -- Turn off `exact ...` trace message
declare_trace library_search         -- Trace a list of all relevant lemmas

meta def library_search : tactic string :=
do [g] ← get_goals | fail "`library_search` should be called with exactly one goal",
   t ← infer_type g,

   -- Collect all definitions with the correct head symbol
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `library_search) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),
   -- Try `apply` followed by `solve_by_elim`, for each definition.
   defs.mfirst apply_declaration,

   -- If something worked, prepare a string to print.
   p ← instantiate_mvars g >>= head_beta >>= pp,
   let r := format!"exact {p}",
   when (¬ is_trace_enabled_for `silence_library_search) $ tactic.trace r,
   return $ to_string r

namespace interactive
/--
`library_search` attempts to apply every definition in the library whose head symbol
matches the goal, and then discharge any new goals using `solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.
-/
meta def library_search := tactic.library_search
end interactive

@[hole_command] meta def library_search_hole_cmd : hole_command :=
{ name := "library_search",
  descr := "Use `library_search` to complete the goal.",
  action := λ _, do
    script ← library_search,
    -- Is there a better API for dropping the 'exact ' prefix on this string?
    return [((script.mk_iterator.remove 6).to_string, "by library_search")] }

end tactic
