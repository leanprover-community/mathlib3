/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen and Scott Morrison
-/

import data.mllist
import tactic.solve_by_elim

/-!
`suggest` and `library_search` are a pair of tactics for applying lemmas from the library to the
current goal.

* `suggest` prints a list of `exact ...` or `refine ...` statements, which may produce new goals
* `library_search` prints a single `exact ...` which closes the goal, or fails
-/

namespace tactic

open native

namespace suggest

/-- compute the head symbol of an expression, but normalise `>` to `<` and `≥` to `≤` -/
-- We may want to tweak this further?
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

/--
A declaration can match the head symbol of the current goal in four possible ways:
* `ex`  : an exact match
* `mp`  : the declaration returns an `iff`, and the right hand side matches the goal
* `mpr` : the declaration returns an `iff`, and the left hand side matches the goal
* `both`: the declaration returns an `iff`, and the both sides match the goal
-/
inductive head_symbol_match
| ex | mp | mpr | both

open head_symbol_match

/-- a textual representation of a `head_symbol_match`, for trace debugging. -/
def head_symbol_match.to_string : head_symbol_match → string
| ex   := "exact"
| mp   := "iff.mp"
| mpr  := "iff.mpr"
| both := "iff.mp and iff.mpr"

/--
When we are determining if a given declaration is potentially relevant for the current goal,
we compute `unfold_head_symbol` on the head symbol of the declaration, producing a list of names.
We consider the declaration potentially relevant if the head symbol of the goal appears in this list.
-/
-- This is a hack.
meta def unfold_head_symbol : name → list name
| `false := [`not, `false]
| n      := [n]

/-- Determine if, and in which way, a given expression matches the specified head symbol. -/
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

/--
Generate a `decl_data` from the given declaration if
it matches the head symbol `hs` for the current goal.
-/
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
-- Phase 1
-- Run `solve_by_elim` on each "safe" goal separately, not worrying about failures.
-- (We only attempt the "safe" goals in this way in Phase 1. In Phase 2 we will do
-- backtracking search across all goals, allowing us to guess solutions that involve data, or
-- unify metavariables, but only as long as we can finish all goals.)
try (any_goals (independent_goal >> solve_by_elim { discharger := discharger })) >>
-- Phase 2
(done <|>
  -- If there were any goals that we did not attempt solving in the first phase
  -- (because they weren't propositional, or contained a metavariable)
  -- as a second phase we attempt to solve all remaining goals at once (with backtracking across goals).
  any_goals (success_if_fail independent_goal) >>
  solve_by_elim { all_goals := tt, discharger := discharger } <|>
  -- and fail unless `close_goals = ff`
  guard ¬ close_goals)

/--
Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the goal using `apply_and_solve`.
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
   if g.has_meta_var then return (sformat!"refine {r}") else return (sformat!"exact {r}")

/--
Assuming that a goal `g` has been (partially) solved in the tactic_state `l`,
this function prepares a string of the form `exact ...` or `refine ...` (possibly with underscores)
that will reproduce that result.
-/
meta def message (g : expr) (l : tactic_state) : tactic string :=
do s ← read,
   write l,
   r ← tactic_statement g,
   write s,
   return r

/-- An `application` records the result of a successful application of a library lemma. -/
meta structure application :=
(state     : tactic_state)
(script    : string)
(decl      : option declaration)
(num_goals : ℕ)
(hyps_used : ℕ)

end suggest

open suggest

declare_trace suggest         -- Trace a list of all relevant lemmas

-- implementation note: we produce a `tactic (mllist tactic application)` first,
-- because it's easier to work in the tactic monad, but in a moment we squash this
-- down to an `mllist tactic application`.
private meta def suggest_core' (discharger : tactic unit := done) :
  tactic (mllist tactic application) :=
focus1 $
do [g] ← get_goals,
   hyps ← local_context,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (lock_tactic_state (do solve_by_elim { discharger := discharger },
          s ← read,
          m ← tactic_statement g,
          g ← instantiate_mvars g,
          return $ mllist.of_list [⟨s, m, none, 0, hyps.countp(λ h, h.occurs g)⟩])) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
   t ← infer_type g,
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `suggest) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),

   -- Try applying each lemma against the goal,
   -- then record the number of remaining goals, and number of local hypotheses used.
   return $ (mllist.of_list defs).mfilter_map
   (λ d, lock_tactic_state $ do
     apply_declaration ff discharger d,
     ng ← num_goals,
     g ← instantiate_mvars g,
     state ← read,
     m ← message g state,
     return
     { application .
       state := state,
       decl := d.d,
       script := m,
       num_goals := ng,
       hyps_used := hyps.countp(λ h, h.occurs g) }))

/--
The core `suggest` tactic.
It attempts to apply a declaration from the library,
then solve new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from the library,
* `script`, a string of the form `refine ...` or `exact ...` which will reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
meta def suggest_core (discharger : tactic unit := done) : mllist tactic application :=
(mllist.monad_lift (suggest_core' discharger)).join

/--
See `suggest_core`.

Returns a list of at most `limit` `application`s,
sorted by number of goals, and then (reverse) number of hypotheses used.
-/
meta def suggest (limit : option ℕ := none) (discharger : tactic unit := done) : tactic (list application) :=
do let results := suggest_core discharger,
   -- Get the first n elements of the successful lemmas
   L ← if h : limit.is_some then results.take (option.get h) else results.force,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   return $ L.qsort(λ d₁ d₂, d₁.num_goals < d₂.num_goals ∨ (d₁.num_goals = d₂.num_goals ∧ d₁.hyps_used ≥ d₂.hyps_used))

/--
Returns a list of at most `limit` strings, of the form `exact ...` or `refine ...`, which make
progress on the current goal using a declaration from the library.
-/
meta def suggest_scripts (limit : option ℕ := none) (discharger : tactic unit := done) : tactic (list string) :=
do L ← suggest limit discharger,
   return $ L.map application.script

/--
Returns a string of the form `exact ...`, which closes the current goal.
-/
meta def library_search (discharger : tactic unit := done) : tactic string :=
(suggest_core discharger).mfirst (λ a, do guard (a.num_goals = 0), write a.state, return a.script)

namespace interactive
open tactic
open interactive
open lean.parser
local postfix `?`:9001 := optional

declare_trace silence_suggest -- Turn off `exact/refine ...` trace messages for `suggest`

/--
`suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.
-/
meta def suggest (n : parse (with_desc "n" small_nat)?) : tactic unit :=
do L ← tactic.suggest_scripts (n.get_or_else 50),
  if is_trace_enabled_for `silence_suggest then
    skip
  else
    if L.length = 0 then
      fail "There are no applicable declarations"
    else
      L.mmap trace >> skip

declare_trace silence_library_search -- Turn off `exact ...` trace message for `library_search

/--
`library_search` attempts to apply every definition in the library whose head symbol
matches the goal, and then discharge any new goals using `solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.
-/
meta def library_search : tactic unit :=
tactic.library_search tactic.done >>=
if is_trace_enabled_for `silence_library_search then
  (λ _, skip)
else
  trace

end interactive

@[hole_command] meta def library_search_hole_cmd : hole_command :=
{ name := "library_search",
  descr := "Use `library_search` to complete the goal.",
  action := λ _, do
    script ← library_search,
    -- Is there a better API for dropping the 'exact ' prefix on this string?
    return [((script.mk_iterator.remove 6).to_string, "by library_search")] }

end tactic
