/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.core

namespace tactic

meta def mk_assumption_set (no_dflt : bool) (hs : list simp_arg_type) (attr : list name): tactic (list expr) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   hs ← hs.mmap i_to_expr_for_apply,
   l ← attr.mmap $ λ a, attribute.get_instances a,
   let l := l.join,
   m ← list.mmap mk_const l,
   let hs := (hs ++ m).filter $ λ h, expr.const_name h ∉ gex,
   hs ← if no_dflt then
          return hs
        else
          do { congr_fun ← mk_const `congr_fun,
               congr_arg ← mk_const `congr_arg,
               return (congr_fun :: congr_arg :: hs) },
   if ¬ no_dflt ∨ all_hyps then do
    ctx ← local_context,
    return $ hs.append (ctx.filter (λ h, h.local_uniq_name ∉ hex)) -- remove local exceptions
   else return hs

meta def solve_by_elim_aux (discharger : tactic unit) (asms : tactic (list expr))  : ℕ → tactic unit
| 0 := done
| (n+1) := done <|>
              (discharger >> solve_by_elim_aux n) <|>
              (apply_assumption asms $ solve_by_elim_aux n)

meta structure by_elim_opt :=
  (all_goals : bool := ff)
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := local_context)
  (max_rep : ℕ := 3)

meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  (if opt.all_goals then id else focus1) $
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
`solve_by_elim` calls `apply_assumption` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply_assumption` on the generated subgoals until no subgoals remain,
performing at most `max_rep` recursive steps.

`solve_by_elim` discharges the current goal or fails

`solve_by_elim` performs back-tracking if `apply_assumption` chooses an unproductive assumption

By default, the assumptions passed to apply_assumption are the local context, `congr_fun` and
`congr_arg`.

`solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas.

`solve_by_elim with attr₁ ... attrᵣ also applied all lemmas tagged with the specified attributes.

`solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `congr_fun`, or `congr_arg`
unless they are explicitly included.

`solve_by_elim [-id]` removes a specified assumption.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments:
- discharger: a subsidiary tactic to try at each step (e.g. `cc` may be helpful)
- max_rep: number of attempts at discharging generated sub-goals
-/
meta def solve_by_elim (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)  (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) : tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_elim { all_goals := all_goals.is_some, assumptions := return asms, ..opt }
end interactive

end tactic
