/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.core

/-!
# solve_by_elim

A depth-first search backwards reasoner.

`solve_by_elim` takes a list of lemmas, and repeating tries to `apply` these against
the goals, recursively acting on any generated subgoals.

It accepts a variety of configuration options described below, enabling
* backtracking across multiple goals,
* pruning the search tree, and
* invoking other tactics before or after trying to apply lemmas.

At present it has no "premise selection", and simply tries the supplied lemmas in order
at each step of the search.
-/

namespace tactic

namespace solve_by_elim
/--
`mk_assumption_set` builds a collection of lemmas for use in
the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congr_fun` and
  `congr_arg`.
* The flag `no_dflt` removes these.
* The argument `hs` is a list of `simp_arg_type`s,
  and can be used to add, or remove, lemmas or expressions from the set.
* The argument `attr : list name` adds all lemmas tagged with one of a specified list of attributes.

`mk_assumption_set` returns not a `list expr`, but a `list (tactic expr) × tactic (list expr)`.
There are two separate problems that need to be solved.

### Relevant local hypotheses

`solve_by_elim*` works with multiple goals,
and we need to use separate sets of local hypotheses for each goal.
The second component of the returned value provides these local hypotheses.
(Essentially using `local_context`, along with some filtering to remove hypotheses
that have been explicitly removed via `only` or `[-h]`.)

### Stuck metavariables

Lemmas with implicit arguments would be filled in with metavariables if we created the
`expr` objects immediately, so instead we return thunks that generate the expressions
on demand. This is the first component, with type `list (tactic expr)`.

As an example, we have `def rfl : ∀ {α : Sort u} {a : α}, a = a`, which on elaboration will become
`@rfl ?m_1 ?m_2`.

Because `solve_by_elim` works by repeated application of lemmas against subgoals,
the first time such a lemma is successfully applied,
those metavariables will be unified, and thereafter have fixed values.
This would make it impossible to apply the lemma
a second time with different values of the metavariables.

See https://github.com/leanprover-community/mathlib/issues/2269

As an optimisation, after we build the list of `tactic expr`s, we actually run them, and replace any
that do not in fact produce metavariables with a simple `return` tactic.
-/
meta def mk_assumption_set (no_dflt : bool) (hs : list simp_arg_type) (attr : list name) :
  tactic (list (tactic expr) × tactic (list expr)) :=
-- We lock the tactic state so that any spurious goals generated during
-- elaboration of pre-expressions are discarded
lock_tactic_state $
do
  -- `hs` are expressions specified explicitly,
  -- `hex` are exceptions (specified via `solve_by_elim [-h]`) referring to local hypotheses,
  -- `gex` are the other exceptions
  (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
  -- Recall, per the discussion above, we produce `tactic expr` thunks rather than actual `expr`s.
  -- Note that while we evaluate these thunks on two occasions below while preparing the list,
  -- this is a one-time cost during `mk_assumption_set`, rather than a cost proportional to the
  -- length of the search `solve_by_elim` executes.
  let hs := hs.map (λ h, i_to_expr_for_apply h),
  l ← attr.mmap $ λ a, attribute.get_instances a,
  let l := l.join,
  let m := l.map (λ h, mk_const h),
  -- In order to remove the expressions we need to evaluate the thunks.
  hs ← (hs ++ m).mfilter $ λ h, (do h ← h, return $ expr.const_name h ∉ gex),
  let hs := if no_dflt then hs else
    ([`rfl, `trivial, `congr_fun, `congr_arg].map (λ n, (mk_const n))) ++ hs,
  let locals : tactic (list expr) := if ¬ no_dflt ∨ all_hyps then do
    ctx ← local_context,
    -- Remove local exceptions specified in `hex`:
    return $ ctx.filter (λ h : expr, h.local_uniq_name ∉ hex)
  else return [],
  -- Finally, run all of the tactics: any that return an expression without metavariables can safely
  -- be replaced by a `return` tactic.
  hs ← hs.mmap (λ h : tactic expr, do
    e ← h,
    if e.has_meta_var then return h else return (return e)),
  return (hs, locals)

/--
Configuration options for `solve_by_elim`.

* `accept : list expr → tactic unit` determines whether the current branch should be explored.
   At each step, before the lemmas are applied,
   `accept` is passed the proof terms for the original goals,
   as reported by `get_goals` when `solve_by_elim` started.
   These proof terms may be metavariables (if no progress has been made on that goal)
   or may contain metavariables at some leaf nodes
   (if the goal has been partially solved by previous `apply` steps).
   If the `accept` tactic fails `solve_by_elim` aborts searching this branch and backtracks.
   By default `accept := λ _, skip` always succeeds.
   (There is an example usage in `tests/solve_by_elim.lean`.)
* `pre_apply : tactic unit` specifies an additional tactic to run before each round of `apply`.
* `discharger : tactic unit` specifies an additional tactic to apply on subgoals
  for which no lemma applies.
  If that tactic succeeds, `solve_by_elim` will continue applying lemmas on resulting goals.
-/
meta structure basic_opt extends apply_any_opt :=
(accept : list expr → tactic unit := λ _, skip)
(pre_apply : tactic unit := skip)
(discharger : tactic unit := failed)
(max_depth : ℕ := 3)

declare_trace solve_by_elim         -- trace attempted lemmas

/--
A helper function for trace messages, prepending '....' depending on the current search depth.
-/
meta def solve_by_elim_trace (n : ℕ) (f : format) : tactic unit :=
trace_if_enabled `solve_by_elim
  (format!"[solve_by_elim {(list.repeat '.' (n+1)).as_string} " ++ f ++ "]")

/-- A helper function to generate trace messages on successful applications. -/
meta def on_success (g : format) (n : ℕ) (e : expr) : tactic unit :=
do
  pp ← pp e,
  solve_by_elim_trace n (format!"✅ `{pp}` solves `⊢ {g}`")

/-- A helper function to generate trace messages on unsuccessful applications. -/
meta def on_failure (g : format) (n : ℕ) : tactic unit :=
solve_by_elim_trace n (format!"❌ failed to solve `⊢ {g}`")

/--
A helper function to generate the tactic that print trace messages.
This function exists to ensure the target is pretty printed only as necessary.
-/
meta def trace_hooks (n : ℕ) : tactic ((expr → tactic unit) × tactic unit) :=
if is_trace_enabled_for `solve_by_elim then
  do
    g ← target >>= pp,
    return (on_success g n, on_failure g n)
else
  return (λ _, skip, skip)

/--
The internal implementation of `solve_by_elim`, with a limiting counter.
-/
meta def solve_by_elim_aux (opt : basic_opt) (original_goals : list expr)
  (lemmas : list (tactic expr)) (ctx : tactic (list expr)) :
  ℕ → tactic unit
| n := do
  -- First, check that progress so far is `accept`able.
  lock_tactic_state (original_goals.mmap instantiate_mvars >>= opt.accept),
  -- Then check if we've finished.
  (done >> solve_by_elim_trace (opt.max_depth - n) "success!") <|> (do
    -- Otherwise, if there's more time left,
    (guard (n > 0) <|>
      solve_by_elim_trace opt.max_depth "🛑 aborting, hit depth limit" >> failed),
    -- run the `pre_apply` tactic, then
    opt.pre_apply,
    -- try either applying a lemma and recursing,
    (on_success, on_failure) ← trace_hooks (opt.max_depth - n),
    ctx_lemmas ← ctx,
    (apply_any_thunk (lemmas ++ (ctx_lemmas.map return)) opt.to_apply_any_opt
      (solve_by_elim_aux (n-1))
      on_success on_failure) <|>
    -- or if that doesn't work, run the discharger and recurse.
     (opt.discharger >> solve_by_elim_aux (n-1)))

/--
Arguments for `solve_by_elim`:
* By default `solve_by_elim` operates only on the first goal,
  but with `backtrack_all_goals := true`, it operates on all goals at once,
  backtracking across goals as needed,
  and only succeeds if it discharges all goals.
* `lemmas` specifies the list of lemmas to use in the backtracking search.
  If `none`, `solve_by_elim` uses the local hypotheses,
  along with `rfl`, `trivial`, `congr_arg`, and `congr_fun`.
* `lemma_thunks` provides the lemmas as a list of `tactic expr`,
  which are used to regenerate the `expr` objects to avoid binding metavariables.
  It should not usually be specified by the user.
  (If both `lemmas` and `lemma_thunks` are specified, only `lemma_thunks` is used.)
* `ctx_thunk` is for internal use only: it returns the local hypotheses which will be used.
* `max_depth` bounds the depth of the search.
-/
meta structure opt extends basic_opt :=
(backtrack_all_goals : bool := ff)
(lemmas : option (list expr) := none)
(lemma_thunks : option (list (tactic expr)) := lemmas.map (λ l, l.map return))
(ctx_thunk : tactic (list expr) := local_context)

/--
If no lemmas have been specified, generate the default set
(local hypotheses, along with `rfl`, `trivial`, `congr_arg`, and `congr_fun`).
-/
meta def opt.get_lemma_thunks (opt : opt) : tactic (list (tactic expr) × tactic (list expr)) :=
match opt.lemma_thunks with
| none := mk_assumption_set ff [] []
| some lemma_thunks := return (lemma_thunks, opt.ctx_thunk)
end

end solve_by_elim

open solve_by_elim

/--
`solve_by_elim` repeatedly tries `apply`ing a lemma
from the list of assumptions (passed via the `opt` argument),
recursively operating on any generated subgoals, backtracking as necessary.

`solve_by_elim` succeeds only if it discharges the goal.
(By default, `solve_by_elim` focuses on the first goal, and only attempts to solve that.
With the option `backtrack_all_goals := tt`,
it attempts to solve all goals, and only succeeds if it does so.
With `backtrack_all_goals := tt`, `solve_by_elim` will backtrack a solution it has found for
one goal if it then can't discharge other goals.)

If passed an empty list of assumptions, `solve_by_elim` builds a default set
as per the interactive tactic, using the `local_context` along with
`rfl`, `trivial`, `congr_arg`, and `congr_fun`.

To pass a particular list of assumptions, use the `lemmas` field
in the configuration argument. This expects an
`option (list expr)`. In certain situations it may be necessary to instead use the
`lemma_thunks` field, which expects a `option (list (tactic expr))`.
This allows for regenerating metavariables
for each application, which might otherwise get stuck.

See also the simpler tactic `apply_rules`, which does not perform backtracking.
-/
meta def solve_by_elim (opt : opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  (lemmas, ctx_lemmas) ← opt.get_lemma_thunks,
  (if opt.backtrack_all_goals then id else focus1) $ (do
    gs ← get_goals,
    solve_by_elim_aux opt.to_basic_opt gs lemmas ctx_lemmas opt.max_depth <|>
    fail ("`solve_by_elim` failed.\n" ++
      "Try `solve_by_elim { max_depth := N }` for `N > " ++ (to_string opt.max_depth) ++ "`\n" ++
      "or use `set_option trace.solve_by_elim true` to view the search."))

setup_tactic_parser

namespace interactive
/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

If this fails, `apply_assumption` will call `symmetry` and try again.

If this also fails, `apply_assumption` will call `exfalso` and try again,
so that if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

Optional arguments:
- `lemmas`: a list of expressions to apply, instead of the local constants
- `tac`: a tactic to run on each subgoal after applying an assumption; if
  this tactic fails, the corresponding assumption will be rejected and
  the next one will be attempted.
-/
meta def apply_assumption
  (lemmas : option (list expr) := none)
  (opt : apply_any_opt := {})
  (tac : tactic unit := skip) : tactic unit :=
do
  lemmas ← match lemmas with
  | none := local_context
  | some lemmas := return lemmas
  end,
  tactic.apply_any lemmas opt tac

add_tactic_doc
{ name        := "apply_assumption",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.apply_assumption],
  tags        := ["context management", "lemma application"] }

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_depth` recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congr_fun` and `congr_arg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas.
* `solve_by_elim with attr₁ ... attrᵣ` also applies all lemmas tagged with the specified attributes.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congr_fun`, or `congr_arg` unless they are explicitly included.
* `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions, removing the specified ones.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments passed via a configuration argument as `solve_by_elim { ... }`
- max_depth: number of attempts at discharging generated sub-goals
- discharger: a subsidiary tactic to try at each step when no lemmas apply
  (e.g. `cc` may be helpful).
- pre_apply: a subsidiary tactic to run at each step before applying lemmas (e.g. `intros`).
- accept: a subsidiary tactic `list expr → tactic unit` that at each step,
    before any lemmas are applied, is passed the original proof terms
    as reported by `get_goals` when `solve_by_elim` started
    (but which may by now have been partially solved by previous `apply` steps).
    If the `accept` tactic fails,
    `solve_by_elim` will abort searching the current branch and backtrack.
    This may be used to filter results, either at every step of the search,
    or filtering complete results
    (by testing for the absence of metavariables, and then the filtering condition).
-/
meta def solve_by_elim (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : solve_by_elim.opt := { }) :
  tactic unit :=
do (lemma_thunks, ctx_thunk) ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_elim
   { backtrack_all_goals := all_goals.is_some ∨ opt.backtrack_all_goals,
     lemma_thunks := some lemma_thunks,
     ctx_thunk := ctx_thunk,
     ..opt }

add_tactic_doc
{ name        := "solve_by_elim",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.solve_by_elim],
  tags        := ["search"] }

end interactive

end tactic
