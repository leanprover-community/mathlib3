/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.solve_by_elim
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

/-- Fail if the target contains a metavariable. -/
meta def no_mvars_in_target : tactic unit :=
do t ← target,
   guard t.list_meta_vars.empty

/--
Apply the lemma `e`, then attempt to close all goals using `solve_by_elim { discharger := discharger }`,
failing if `close_goals = tt` and there are any goals remaining.
-/
-- Implementation note: as this is used by both `library_search` and `suggest`,
-- we first run `solve_by_elim` separately on a subset of the goals, whether or not `close_goals` is set,
-- and then if `close_goals = tt`, require that `solve_by_elim { all_goals := tt }` succeeds
-- on the remaining goals.
meta def apply_and_solve (close_goals : bool) (discharger : tactic unit) (e : expr) : tactic unit :=
apply e >>
-- run `solve_by_elim` on each propositional goal separately, not worrying if it ever fails
try (any_goals (propositional_goal >> no_mvars_in_target >> solve_by_elim { discharger := discharger })) >>
-- now, if any goals remain, run `solve_by_elim` on them all together
(done <|>
  solve_by_elim { all_goals := tt, discharger := discharger } <|>
  -- and fail unless `close_goals = ff`
  guard ¬ close_goals)

/--
Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the goal using `solve_by_elim`.
-/
meta def apply_declaration (close_goals : bool) (discharger : tactic unit) (d : decl_data) : tactic unit :=
let tac := apply_and_solve close_goals discharger in
do (e, t) ← decl_mk_const d.d,
   match d.m with
   | ex   := tac e
   | mp   := do l ← iff_mp_core e t, tac l
   | mpr  := do l ← iff_mpr_core e t, tac l
   | both :=
      (do l ← iff_mp_core e t, tac l) <|>
      (do l ← iff_mpr_core e t, tac l)
   end

/--
Replace any metavariables in the expression with underscores, in preparation for printing
`refine ...` statements.
-/
meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_mvar then some (unchecked_cast pexpr.mk_placeholder) else none)

/--
Construct a `refine ...` or `exact ...` string which would construct `g`.
-/
meta def tactic_statement (g : expr) : tactic string :=
do g ← instantiate_mvars g,
   g ← head_beta g,
   r ← pp (replace_mvars g),
   r ← pure $ if g.has_meta_var then sformat!"refine {r}" else sformat!"exact {r}",
   if g.has_meta_var then sformat!"refine {r}" else sformat!"exact {r}"

end library_search

open library_search
open library_search.head_symbol_match

declare_trace silence_library_search -- Turn off `exact ...` trace message
declare_trace library_search         -- Trace a list of all relevant lemmas

meta def library_search (discharger : tactic unit := done) : tactic string :=
do [g] ← get_goals | fail "`library_search` should be called with exactly one goal",
   t ← infer_type g,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   solve_by_elim { discharger := discharger } <|> (do
   -- Collect all definitions with the correct head symbol
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `library_search) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),
   -- Try `apply` followed by `solve_by_elim`, for each definition.
   defs.mfirst (apply_declaration tt discharger)),

   -- If something worked, prepare a string to print.
   r ← tactic_statement g,
   when (¬ is_trace_enabled_for `silence_library_search) $ tactic.trace r,
   return $ to_string r

namespace interactive
open lean.parser interactive

/--
`library_search` attempts to apply every definition in the library whose head symbol
matches the goal, and then discharge any new goals using `solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.
-/
meta def library_search :=
tactic.library_search tactic.done

end interactive

@[hole_command] meta def library_search_hole_cmd : hole_command :=
{ name := "library_search",
  descr := "Use `library_search` to complete the goal.",
  action := λ _, do
    script ← library_search,
    -- Is there a better API for dropping the 'exact ' prefix on this string?
    return [((script.mk_iterator.remove 6).to_string, "by library_search")] }

end tactic
