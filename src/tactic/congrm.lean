/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Damiano Testa
-/
import tactic.interactive

/-!  `congrm`: `congr` with pattern-matching -/

namespace tactic

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
  cl ← mk_specialized_congr_lemma pat,
  H_congr_lemma ← assertv `H_congr_lemma cl.type cl.proof,
  [prf] ← get_goals,
  apply H_congr_lemma,
  all_goals' $ try $ clear H_congr_lemma,
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

/--  Scans three `expr`s `e, lhs, rhs` in parallel.
Currently, `equate_with_pattern_1` has three behaviours at each location:
produce a goal, recurse, or skip.

See the doc-string for `tactic.interactive.congrm_1` for more details.
-/
meta def equate_with_pattern_1 : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el,
    rotate,
    get_local n >>= rewrite_target,
    equate_with_pattern_1 f f0 f1
  | _ := do equate_with_pattern_1 e e0 e1 *> equate_with_pattern_1 f f0 f1
  end
| _ _ _ := skip

/--  `congrm_1 e` assumes that the goal is of the form `lhs = rhs`.
`congrm_1 e` scans `e, lhs, rhs` in parallel.
Assuming that the three expressions are successions of function applications, `congrm_1 e`
uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

If `e` has a meta-variable in a location, then the tactic produces a side-goal with
the equality of the corresponding locations in `lhs, rhs`.

Otherwise, `congrm_1` keeps scanning deeper into the expressions, until either the expressions
finish or there is a mismatch between their shapes.

*Note:* `congrm_1` does no check to make sure that the functions that it is matching are equal,
or even defeq.  For instance,
```lean
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  congrm_1 (id _) + nat.succ _,
end
```
produces the three goals
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
In fact, not even the types need to match:
```
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  let i₁ : ℤ → ℤ := sorry,
  let i₁' : ℤ → ℤ := sorry,
  let i₂ : ℤ → ℤ → ℤ := sorry,
  congrm_1 i₂ (i₁ _) (i₁' _),
end
```
produces the same three goals as above
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
-/
meta def congrm_1 (arg : parse texpr) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  equate_with_pattern_1 ta lhs rhs,
  try refl,
  get_goals >>= (λ g, set_goals g.reverse)  -- reverse the order of the goals

end tactic.interactive
