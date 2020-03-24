/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.core

namespace tactic

/--
Builds a collection of lemmas for use in the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congr_fun` and
  `congr_arg`.
* The flag `no_dflt` removes these.
* The argument `hs` is a list of `simp_arg_type`s,
  and can be used to add, or remove, lemmas or expressions from the set.
* The argument `attr : list name` adds all lemmas tagged with one of a specified list of attributes.
-/
meta def mk_assumption_set (no_dflt : bool) (hs : list simp_arg_type) (attr : list name) :
  tactic (list expr) :=
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
meta def solve_by_elim_aux (discharger : tactic unit) (lemmas : list expr)  : ℕ → tactic unit
| 0 := done
| (n+1) := done <|>
    (apply_any lemmas $ solve_by_elim_aux n) <|>
    (discharger >> solve_by_elim_aux n)

/--
Configuration options for `solve_by_elim`.

* By default `solve_by_elim` operates only on the first goal,
  but with `backtrack_all_goals := true`, it operates on all goals at once,
  backtracking across goals as needed,
  and only succeeds if it discharges all goals.
* `discharger` specifies an additional tactic to apply on subgoals for which no lemma applies.
  If that tactic succeeds, `solve_by_elim` will continue applying lemmas on resulting goals.
* `assumptions` generates the list of lemmas to use in the backtracking search.
* `max_steps` bounds the depth of the search.
-/
meta structure by_elim_opt :=
  (backtrack_all_goals : bool := ff)
  (discharger : tactic unit := done)
  (lemmas : list expr := [])
  (max_steps : ℕ := 3)

meta def by_elim_opt.get_lemmas (opt : by_elim_opt) : tactic (list expr) :=
if opt.lemmas = [] then mk_assumption_set ff [] [] else return opt.lemmas

/--
`solve_by_elim` repeatedly tries `apply`ing a lemma
from the list of assumptions (passed via the `by_elim_opt` argument),
recursively operating on any generated subgoals.

It succeeds only if it discharges the first goal
(or with `backtrack_all_goals := tt`, if it discharges all goals.)

If passed an empty list of assumptions, `solve_by_elim` builds a default set
as per the interactive tactic, using the `local_context` along with
`rfl`, `trivial`, `congr_arg`, and `congr_fun`.
-/
meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  lemmas ← opt.get_lemmas,
  (if opt.backtrack_all_goals then id else focus1) $
    solve_by_elim_aux opt.discharger lemmas opt.max_steps

open interactive lean.parser interactive.types
local postfix `?`:9001 := optional

namespace interactive
/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

If this fails, `apply_assumption` will call `symmetry` and try again.

If this also fails, `apply_assumption` will call `exfalso` and try again,
so that if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

Optional arguments:
- lemmas: a list of expressions to apply, instead of the local constants
- tac: a tactic to run on each subgoal after applying an assumption; if
  this tactic fails, the corresponding assumption will be rejected and
  the next one will be attempted.
-/
meta def apply_assumption
  (lemmas : list expr := [])
  (tac : tactic unit := skip) : tactic unit :=
do
  lemmas ← if lemmas = [] then local_context else return lemmas,
  tactic.apply_any lemmas tac

add_tactic_doc
{ name        := "apply_assumption",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.apply_assumption],
  tags        := [] }

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_steps` recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congr_fun` and `congr_arg`.

`solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas.

`solve_by_elim with attr₁ ... attrᵣ` also applies all lemmas tagged with the specified attributes.

`solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `rfl`, `trivial`,
`congr_fun`, or `congr_arg` unless they are explicitly included.

`solve_by_elim [-id]` removes a specified assumption.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments:
- discharger: a subsidiary tactic to try at each step (e.g. `cc` may be helpful)
- max_steps: number of attempts at discharging generated sub-goals

---

The tactic `solve_by_elim` repeatedly applies assumptions to the current goal, and succeeds if this
eventually discharges the main goal.
```lean
solve_by_elim { discharger := `[cc] }
```
also attempts to discharge the goal using congruence closure before each round of applying
assumptions.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

By default `solve_by_elim` also applies `congr_fun` and `congr_arg` against the goal.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas (or all lemmas tagged with the
  named attributes).
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `congr_fun`, or
  `congr_arg` unless they are explicitly included.
* `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions, removing the specified ones.

-/
meta def solve_by_elim (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) :
  tactic unit :=
do lemmas ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_elim
   { backtrack_all_goals := all_goals.is_some ∨ opt.backtrack_all_goals,
     lemmas := lemmas,
     ..opt }

add_tactic_doc
{ name        := "solve_by_elim",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.solve_by_elim],
  tags        := ["search"] }

end interactive

end tactic
