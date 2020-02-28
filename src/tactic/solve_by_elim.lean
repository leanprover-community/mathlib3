/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.core

namespace tactic

/--
Builds a collection of lemmas for use in the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congr_fun` and `congr_arg`.
* The flag `no_dflt` removes these.
* The argument `hs` is a list of `simp_arg_type`s,
  and can be used to add, or remove, lemmas or expressions from the set.
* The argument `attr : list name` adds all lemmas tagged with one of a specified list of attributes.
-/
meta def mk_assumption_set (no_dflt : bool) (hs : list simp_arg_type) (attr : list name) : tactic (list expr) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   hs ← hs.mmap i_to_expr_for_apply,
   l ← attr.mmap $ λ a, attribute.get_instances a,
   let l := l.join,
   m ← list.mmap mk_const l,
   let hs := (hs ++ m).filter $ λ h, expr.const_name h ∉ gex,
   hs ← if no_dflt then
          return hs
        else
          do { rfl_const ← mk_const `rfl,
               trivial_const ← mk_const `trivial,
               congr_fun ← mk_const `congr_fun,
               congr_arg ← mk_const `congr_arg,
               return (rfl_const :: trivial_const :: congr_fun :: congr_arg :: hs) },
   if ¬ no_dflt ∨ all_hyps then do
    ctx ← local_context,
    return $ hs.append (ctx.filter (λ h, h.local_uniq_name ∉ hex)) -- remove local exceptions
   else return hs

/--
The internal implementation of `solve_by_elim`, with a limiting counter.
-/
meta def solve_by_elim_aux (discharger : tactic unit) (asms : tactic (list expr))  : ℕ → tactic unit
| 0 := done
| (n+1) := done <|>
              (apply_assumption asms $ solve_by_elim_aux n) <|>
              (discharger >> solve_by_elim_aux n)

/--
Configuration options for `solve_by_elim`.

* By default `solve_by_elim` operates only on the first goal,
  but with `backtrack_all_goals := true`, it operates on all goals at once,
  backtracking across goals as needed,
  and only succeeds if it dischargers all goals.
* `discharger` specifies a tactic to try discharge subgoals
  (this is only attempted on subgoals for which no lemma applies successfully).
* `assumptions` generates the list of lemmas to use in the backtracking search.
* `max_rep` bounds the depth of the search.
-/
meta structure by_elim_opt :=
  (backtrack_all_goals : bool := ff)
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := mk_assumption_set false [] [])
  (max_rep : ℕ := 3)

/--
`solve_by_elim` repeatedly tries `apply`ing a lemma
from the list of assumptions (passed via the `by_elim_opt` argument),
recursively operating on any generated subgoals.
It succeeds only if it discharges the first goal
(or with `backtrack_all_goals := tt`, if it discharges all goals.)
-/
meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  (if opt.backtrack_all_goals then id else focus1) $
    solve_by_elim_aux opt.discharger opt.assumptions opt.max_rep

open interactive lean.parser interactive.types
local postfix `?`:9001 := optional

namespace interactive
/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

alternatively, when encountering an assumption of the form `sg₀ → ¬ sg₁`,
after the main approach failed, the goal is dismissed and `sg₀` and `sg₁`
are made into the new goal.

optional arguments:
- asms: list of rules to consider instead of the local constants
- tac:  a tactic to run on each subgoals after applying an assumption; if
        this tactic fails, the corresponding assumption will be rejected and
        the next one will be attempted.
-/
meta def apply_assumption
  (asms : tactic (list expr) := local_context)
  (tac : tactic unit := return ()) : tactic unit :=
tactic.apply_assumption asms tac

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_rep` recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if `apply_assumption` chooses an unproductive assumption.

By default, the assumptions passed to apply_assumption are the local context, `rfl`, `trivial`, `congr_fun` and
`congr_arg`.

`solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas.

`solve_by_elim with attr₁ ... attrᵣ also applied all lemmas tagged with the specified attributes.

`solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `rfl`, `trivial`, `congr_fun`, or `congr_arg`
unless they are explicitly included.

`solve_by_elim [-id]` removes a specified assumption.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments:
- discharger: a subsidiary tactic to try at each step (e.g. `cc` may be helpful)
- max_rep: number of attempts at discharging generated sub-goals
-/
meta def solve_by_elim (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) : tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_elim
   { backtrack_all_goals := all_goals.is_some ∨ opt.backtrack_all_goals,
     assumptions := return asms,
     ..opt }
end interactive

end tactic
