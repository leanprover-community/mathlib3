/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import measure_theory.integral.fund_thm_calculus
import analysis.normed_space.exponential
import analysis.quaternion
import algebra.lie.of_associative
import analysis.special_functions.exponential

/-! More lemmas aboutderiviatives of `exp`.

This follows https://physics.stackexchange.com/a/41671/185147. -/

variables {𝔸 𝔹 : Type*}
variables [normed_ring 𝔸] [normed_algebra ℝ 𝔸] [complete_space 𝔸]

-- to make the goal view readable
notation (name := deriv) `∂` binders `, ` r:(scoped:67 f, deriv f) := r
local notation `e` := exp ℝ

lemma has_deriv_at_exp_smul_const (A : 𝔸) (t : ℝ) :
  has_deriv_at (λ t : ℝ, exp ℝ (t • A)) (A * exp ℝ (t • A)) t := sorry

lemma has_deriv_at_exp_smul_const' (A : 𝔸) (t : ℝ) :
  has_deriv_at (λ t : ℝ, exp ℝ (t • A)) (exp ℝ (t • A) * A) t :=
begin
  convert has_deriv_at_exp_smul_const A t using 1,
  refine commute.exp_left _ _,
  refine (commute.refl _).smul_left _,
end

lemma deriv_exp_aux (A : ℝ → 𝔸) (r t : ℝ)
  (hA : differentiable_at ℝ A r) :
  exp ℝ (-t • A r) * deriv (λ x, exp ℝ (t • A x)) r =
    (∫ s : ℝ in 0..t, exp ℝ (-s • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  revert t,
  rw ←function.funext_iff,
  -- two functions agree if their derivatives agree and they agree at zero.
  do { `(%%lhs = %%rhs) ← tactic.target,
    let t := ``(%%lhs 0 = %%rhs 0 ∧ deriv %%lhs = deriv %%rhs),
    tactic.interactive.suffices none (some t)},
  { sorry },
  split,
  { simp },
  { ext t,
    rw interval_integral.deriv_integral_right,
    { rw deriv_mul,
      have deriv_comm : deriv (λ (y : ℝ), deriv (λ (x : ℝ), exp ℝ (y • A x)) r) t =
        deriv (λ (x : ℝ), deriv (λ (y : ℝ), exp ℝ (y • A x)) t) r,
      { -- this one is probably really annoying
        sorry },
      { rw deriv_comm,
        simp_rw [(has_deriv_at_exp_smul_const _ _).deriv],
        rw deriv_mul,
        simp_rw [mul_add, ←add_assoc, ←mul_assoc],
        rw [add_right_comm],
        convert zero_add _,
        rw [←add_mul],
        convert zero_mul _,
        rw [←(has_deriv_at_exp_smul_const' _ _).deriv, ←eq_neg_iff_add_eq_zero],
        change deriv ((λ t : ℝ, exp ℝ (t • A r)) ∘ has_neg.neg) t = _,
        rw [deriv.scomp t, deriv_neg, neg_one_smul],
        { exact (has_deriv_at_exp_smul_const _ _).differentiable_at },
        { exact differentiable_at_id.neg },
        { apply_instance },
        { apply_instance },
        { exact hA },
        { change differentiable_at ℝ (exp ℝ ∘ _) _,
          refine differentiable_at.comp _ _ (hA.const_smul _),
          -- uh oh, this looks circular
          sorry }, },
      { exact ((has_deriv_at_exp_smul_const _ _).scomp _ (has_deriv_at_neg _)).differentiable_at },
      sorry },
    { sorry },
    { sorry },
    { refine (continuous_at.mul _ continuous_at_const).mul _,
      sorry,
      sorry, }, },
end

/-- Non-commutative version of `deriv_exp`. -/
lemma deriv_exp' (A : ℝ → 𝔸) (r : ℝ) (h : differentiable_at ℝ A r) :
  deriv (λ x, exp ℝ (A x)) r = (∫ s : ℝ in 0..1, exp ℝ ((1 - s) • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  apply (is_unit_exp ℝ (-A r)).mul_left_cancel,
  have := deriv_exp_aux A r 1 h,
  simp_rw [neg_one_smul, one_smul] at this,
  -- have hA : ∀ r s : ℝ, commute (A r) (-s • A r) := λ r s, commute.refl,
  simp_rw [sub_eq_add_neg, add_smul, one_smul,
    @exp_add_of_commute ℝ _ _ _ _ _ _ _ ((commute.refl (A _)).smul_right _)],
  rw this,
  -- `integral_const_mul` is not general enough!
  sorry,
end

/-- Non-commutative version of `has_deriv_at_exp`. -/
lemma has_deriv_at_exp' (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin
  sorry,
end
