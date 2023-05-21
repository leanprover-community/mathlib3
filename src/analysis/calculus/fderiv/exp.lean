import measure_theory.integral.fund_thm_calculus

import analysis.normed_space.exponential
import analysis.quaternion
import algebra.lie.of_associative
.

open_locale quaternion
example (q : ℍ[ℝ]) (f : ℝ → ℍ[ℝ]) : ∫ t : ℝ in 0..1, q * f t = q * ∫ t : ℝ in 0..1, f t :=
sorry


variables {𝔸 𝔹 : Type*}
variables [normed_ring 𝔸] [normed_algebra ℝ 𝔸] [complete_space 𝔸]
.


notation (name := deriv)
  `∂` binders `, ` r:(scoped:67 f, deriv f) := r

local notation `e` := exp ℝ

#check finset.sum
lemma bar_deriv (A : ℝ → 𝔸) (r t : ℝ) :
  exp ℝ (-t • A r) * deriv (λ x, exp ℝ (t • A x)) r = (∫ s : ℝ in 0..t, exp ℝ (-s • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  have h₁ : ∀ x t, deriv (λ t : ℝ, exp ℝ (t • A x)) t = A x * exp ℝ (t • A x),
  { sorry },
  have h₂ : ∀ x t, deriv (λ t : ℝ, exp ℝ (t • A x)) t = exp ℝ (t • A x) * A x,
  { intros x t,
    rw [h₁],
    refine commute.exp_right _ _,
    refine (commute.refl _).smul_right _, },
  -- have :
  --   exp ℝ (-t • A r) * ⁅(λ B : ℝ → 𝔸, deriv B r), (λ B : ℝ → 𝔸, A r * B r)⁆ (λ r, exp ℝ (t • A r)) =
  --     exp ℝ (-t • A r) * deriv A r * exp ℝ (t • A r),
  -- {
  --   simp only [ring.lie_def, pi.mul_def, mul_assoc],
  --   rw [sub_eq_add_neg, pi.add_def, pi.neg_def],
  --   dsimp only,
  --   congr' 1,
  --   rw add_neg_eq_iff_eq_add,
  --   simp_rw[←mul_assoc,← h₁, mul_assoc, ←h₁],
  --   rw [mul_add],
  --   erw @pi.sub_apply (ℝ → 𝔸) (λ _, 𝔸),
  --   simp only,
  --   sorry },
  -- sorry,
  revert t,
  rw ←function.funext_iff,
  apply_fun deriv,
  ext t,
  rw interval_integral.deriv_integral_right,
  rw deriv_mul,
  have deriv_comm : deriv (λ (y : ℝ), deriv (λ (x : ℝ), exp ℝ (y • A x)) r) t =
    deriv (λ (x : ℝ), deriv (λ (y : ℝ), exp ℝ (y • A x)) t) r,
  { sorry },
  { rw deriv_comm,
    simp_rw [h₁],
    rw deriv_mul,
    simp_rw [mul_add, ←add_assoc, ←mul_assoc],
    rw [add_right_comm],
    convert zero_add _,
    rw [←add_mul],
    convert zero_mul _,
    rw [←h₂, ←eq_neg_iff_add_eq_zero],
    have := @deriv.comp _ _,},
  sorry,
  sorry
end

lemma foo_deriv (A : ℝ → 𝔸) (r : ℝ) :
  deriv (λ x, exp ℝ (A x)) r = (∫ s : ℝ in 0..1, exp ℝ ((1 - s) • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  apply (is_unit_exp ℝ (-A r)).mul_left_cancel,
  have := bar_deriv A r 1,
  simp_rw [neg_one_smul, one_smul] at this,
  have hA : ∀ r s : ℝ, commute (A r) (-s • A r) := sorry,
  simp_rw [sub_eq_add_neg, add_smul, one_smul, λ r s, @exp_add_of_commute ℝ 𝔸 _ _ _ _ _ _ (hA r s)],
  rw this,
  sorry,
  -- rw interval_integral.integral_const_mul,
end

lemma bar_deriv_at (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin

end


lemma foo (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin

end
