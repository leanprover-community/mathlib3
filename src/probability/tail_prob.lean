import probability.notation
import measure_theory.integral.interval_integral

/-
Tail probability states: if `X` is a nonnegative random variable, then
$$\mathbb{E}[X^p] = p \int_0^\infty t^{p - 1} \mathbb{P}(X \ge t) \lambda(dt).$$
-/

open_locale probability_theory nnreal ennreal

namespace measure_theory

open interval_integral

variables {α : Type*} [measurable_space α] {μ : measure α} [is_finite_measure μ]
  {X : α → ℝ} {p : ℕ}

lemma aux1 (hp : p ≠ 0) (x : ℝ) : x ^ p = ∫ t in 0..x, p * t ^ (p - 1) :=
begin
  have : deriv (λ t, t ^ p) = (λ t : ℝ, ↑p * t ^ (p - 1)),
  { ext x, rw deriv_pow },
  rw [integral_deriv_eq_sub' _ this _
    (continuous_const.mul (continuous_pow (p - 1))).continuous_on],
  { simp only [zero_pow (zero_lt_iff.2 hp), sub_zero] },
  { rintro t ht,
    simp only [differentiable_at.pow, differentiable_at_id'] },
end

-- rw using moments once #14755 is merged
theorem foo (hX : 0 ≤ X) (hm : measurable X) :
  μ[X ^ p] = p * ∫ x in {x : ℝ | 0 ≤ x}, x ^ (p - 1) * (μ {ω | x ≤ X ω}).to_real :=
begin
  have hinteq : ∫ ω, (X ^ p) ω ∂μ = ∫ x, x ^ p ∂ (μ.map X),
  { rw integral_map hm.ae_measurable,
    { refl },
    { measurability } },
  rw hinteq,
  sorry
end


end measure_theory
