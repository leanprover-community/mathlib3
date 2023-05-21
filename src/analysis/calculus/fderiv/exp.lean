import measure_theory.integral.fund_thm_calculus

import analysis.normed_space.exponential
import analysis.quaternion
.

open_locale quaternion
example (q : ℍ[ℝ]) (f : ℝ → ℍ[ℝ]) : ∫ t : ℝ in 0..1, q * f t = q * ∫ t : ℝ in 0..1, f t :=
sorry


variables {𝔸 𝔹 : Type*}
variables [normed_ring 𝔸] [normed_algebra ℝ 𝔸] [complete_space 𝔸]
.
#check continuous.deriv_integral

lemma bar_deriv (A : ℝ → 𝔸) (r t : ℝ) :
  exp ℝ (-t • A r) * deriv (λ x, exp ℝ (t • A x)) r = (∫ s : ℝ in 0..t, exp ℝ (-s • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
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
end

lemma bar_deriv_at (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin

end


lemma foo (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin

end
