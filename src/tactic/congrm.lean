/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Damiano Testa
-/
import tactic.interactive

/-!  `congrm`: `congr` with pattern-matching -/

namespace tactic

/--  A generic function with one argument.  It is the "function underscore" input to `congrm`. -/
def congrm_fun1 {α ρ} {r : ρ} : α → ρ := λ _, r
notation `_₁` := congrm_fun1

/--  A generic function with two arguments.  It is the "function underscore" input to `congrm`. -/
def congrm_fun2 {α β ρ} {r : ρ} : α → β → ρ := λ _ _, r
notation `_₂` := congrm_fun2

/--  A generic function with three arguments.  It is the "function underscore" input to `congrm`. -/
def congrm_fun3 {α β γ ρ} {r : ρ} : α → β → γ → ρ := λ _ _ _, r
notation `_₃` := congrm_fun3

/--  A generic function with four arguments.  It is the "function underscore" input to `congrm`. -/
def congrm_fun4 {α β γ δ ρ} {r : ρ} : α → β → γ → δ → ρ := λ _ _ _ _, r
notation `_₄` := congrm_fun4

/--  Replaces a "function underscore" input to `congrm` into the correct expression,
read off from the left-hand-side of the target expression. -/
meta def convert_to_explicit (pat lhs : expr) : tactic expr :=
if pat.get_app_fn.const_name = ``tactic.congrm_fun4 then
  match lhs with
  | (expr.app (expr.app (expr.app (expr.app mr ma) mb) mc) md) := do
    let arg_list := [ma, mb, mc, md],
    [ta, tb, tc, td] ← arg_list.mmap infer_type,
    att ← to_expr ``((λ (x : %%ta) (y : %%tb) (z : %%tc) (w : %%td), %%mr x y z w)) tt ff,
    return $ att.app_of_list $ pat.get_app_args.drop $ arg_list.length + 2
  | _ := fail "not a quadruple function application"
  end
else
if pat.get_app_fn.const_name = ``tactic.congrm_fun3 then
  match lhs with
  | (expr.app (expr.app (expr.app mr ma) mb) mc) := do
    let arg_list := [ma, mb, mc],
    [ta, tb, tc] ← arg_list.mmap infer_type,
    att ← to_expr ``((λ (x : %%ta) (y : %%tb) (z : %%tc), %%mr x y z)) tt ff,
    return $ att.app_of_list $ pat.get_app_args.drop $ arg_list.length + 2
  | _ := fail "not a triple function application"
  end
else
if pat.get_app_fn.const_name = ``tactic.congrm_fun2 then
  match lhs with
  | (expr.app (expr.app mr ma) mb) := do
    let arg_list := [ma, mb],
    [ta, tb] ← arg_list.mmap infer_type,
  att ← to_expr ``((λ (x : %%ta) (y : %%tb), %%mr x y)) tt ff,
  return $ att.app_of_list $ pat.get_app_args.drop $ arg_list.length + 2
  | _ := fail "not a double function application"
  end
else
if pat.get_app_fn.const_name = ``tactic.congrm_fun1 then
  match lhs with
  | (expr.app mr ma) := do
    let arg_list := [ma],
    [ta] ← arg_list.mmap infer_type,
  att ← to_expr ``((λ (x : %%ta), %%mr x)) tt ff,
  return $ att.app_of_list $ pat.get_app_args.drop $ arg_list.length + 2
  | e := fail "not a single function application"
  end
else
return pat

/--
For each element of `list congr_arg_kind` that is `eq`, add a pair `(g, pat)` to the
final list.  Otherwise, discard an appropriate number of initial terms from each list
(possibly none from the first) and repeat.

`pat` is the given pattern-piece at the appropriate location, extracted from the last `list expr`.
It appears to be the list of arguments of a function application.

`g` is possibly the proof of an equality?  It is extracted from the first `list expr`.
-/
private meta def extract_subgoals : list expr → list congr_arg_kind → list expr →
  tactic (list (expr × expr))
| (_ :: _ :: g :: prf_args) (congr_arg_kind.eq :: kinds)             (pat :: pat_args) :=
  (λ rest, (g, pat) :: rest) <$> extract_subgoals prf_args kinds pat_args
| (_ :: prf_args)           (congr_arg_kind.fixed :: kinds)          (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| prf_args                  (congr_arg_kind.fixed_no_param :: kinds) (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| (_ :: _ :: prf_args)      (congr_arg_kind.cast :: kinds)           (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| _ _ [] := pure []
| _ _ _ := fail "unsupported congr lemma"

/--
`equate_with_pattern_core pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
Returns the list of metavariables for the new subgoals at the leafs.
Calls `set_goals []` at the end.
-/
meta def equate_with_pattern_core : expr → tactic (list expr) | pat :=
(applyc ``subsingleton.elim >> pure []) <|>
(applyc ``rfl >> pure []) <|>
if pat.is_mvar || pat.get_delayed_abstraction_locals.is_some then do
  try $ applyc ``_root_.propext,
  get_goals <* set_goals []
else if pat.is_app then do
  `(%%lhs = %%rhs) ← target,
  pat ← convert_to_explicit pat lhs,
  cl ← mk_specialized_congr_lemma pat,
  H_congr_lemma ← assertv `H_congr_lemma cl.type cl.proof,
  [prf] ← get_goals,
  apply H_congr_lemma <|> fail "could not apply congr_lemma",
  all_goals' $ try $ clear H_congr_lemma,  -- given the `set_goals []` that follows, is this needed?
  set_goals [],
  prf ← instantiate_mvars prf,
  subgoals ← extract_subgoals prf.get_app_args cl.arg_kinds pat.get_app_args,
  subgoals ← subgoals.mmap (λ ⟨subgoal, subpat⟩, do
    set_goals [subgoal],
    equate_with_pattern_core subpat),
  pure subgoals.join
else if pat.is_lambda then do
  applyc ``_root_.funext,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.lambda_body.instantiate_var x
else if pat.is_pi then do
  applyc ``_root_.pi_congr,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.pi_codomain.instantiate_var x
else do
  pat ← pp pat,
  fail $ to_fmt "unsupported pattern:\n" ++ pat

/--
`equate_with_pattern pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
The subgoals for the leafs are prepended to the goals.
--/
meta def equate_with_pattern (pat : expr) : tactic unit := do
congr_subgoals ← solve1 (equate_with_pattern_core pat),
gs ← get_goals,
set_goals $ congr_subgoals ++ gs

end tactic

namespace tactic.interactive
open tactic interactive
setup_tactic_parser

/--
`congrm e` assumes that the goal is of the form `lhs = rhs` or `lhs ↔ rhs`.
`congrm e` scans `e, lhs, rhs` in parallel.
Assuming that the three expressions are successions of function applications, `congrm e`
uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

If `e` has a meta-variable in a location, then the tactic produces a side-goal with
the equality of the corresponding locations in `lhs, rhs`.

If `e` is a function application, it applies the automatically generateed congruence lemma
(like `tactic.congr`).

If `e` is a lambda abstraction, it applies `funext`.  If `e` is a pi, it applies `pi_congr`.

Subexpressions that are defeq or whose type is a subsingleton are skipped.

```
example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  -- produces one goal for the underscore: ⊢ a = b
  exact h,
end
```
-/
meta def congrm (arg : parse texpr) : tactic unit := do
try $ applyc ``_root_.eq.to_iff,
`(@eq %%ty _ _) ← target | fail "congrm: goal must be an equality or iff",
ta ← to_expr ``((%%arg : %%ty)) tt ff,
equate_with_pattern ta

add_tactic_doc
{ name := "congrm",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.congrm],
  tags := ["congruence"] }

end tactic.interactive
