import analysis.complex.cauchy_integral

variables
{E : Type*} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
[topological_space.second_countable_topology E] [complete_space E]

open real
open_locale nnreal real

theorem liouville₀ {f : ℂ → E} (h : differentiable ℂ f) {R : ℝ≥0} (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f 0 1) 0 R :=
(h.differentiable_on.has_fpower_series_on_ball zero_lt_one).exchange_radius
  (h.differentiable_on.has_fpower_series_on_ball hR)

theorem liouville₁ {f : ℂ → E} (h : differentiable ℂ f) {R : ℝ≥0} (hR : 0 < R) :
  cauchy_power_series f 0 1 = cauchy_power_series f 0 R :=
has_fpower_series_at.eq_formal_multilinear_series
  ((h.differentiable_on.has_fpower_series_on_ball zero_lt_one).has_fpower_series_at)
  ((h.differentiable_on.has_fpower_series_on_ball hR).has_fpower_series_at)

theorem liouville₂ {f : ℂ → E} (h : differentiable ℂ f) {R : ℝ≥0} (hR : 0 < R) : ∀ (n : ℕ),
  ∥cauchy_power_series f 0 1 n∥ ≤
    (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) * (|R|⁻¹) ^ n :=
by simpa only [liouville₁ h hR] using norm_cauchy_power_series_le f 0 R

open interval_integral
theorem liouville₃ {f : ℂ → E} (h : differentiable ℂ f) {C : ℝ} (hC : ∀ z, ∥f z∥ ≤ C)
  {R : ℝ≥0} (hR : 0 < R) : ∀ (n : ℕ),
  ∥cauchy_power_series f 0 1 n∥ ≤ C * (R⁻¹) ^ n :=
begin
  intro n,
  have h₁ : (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) ≤ (∫ θ : ℝ in 0..2*π, C),
    from integral_mono two_pi_pos.le h.continuous.norm.continuous_on.circle_integrable'
      (by simp) (λ θ, hC _),
  have h₂ : (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, C),
    from (mul_le_mul_left (inv_pos.mpr two_pi_pos)).mpr h₁,
  have h₃ : (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) * (|R|⁻¹) ^ n ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, C) * (|R|⁻¹) ^ n,
    from mul_le_mul_of_nonneg_right h₂ (by simp),
  have h₄ := calc
    ∥cauchy_power_series f 0 1 n∥
      ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) * (|R|⁻¹) ^ n
      : liouville₂ h hR n
  ... ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, C) * (|R|⁻¹) ^ n
      : h₃
  ... = (2 * π)⁻¹ * (2 * π * C) * (R⁻¹) ^ n
      : by simp only [integral_const, sub_zero, algebra.id.smul_eq_mul, nnreal.abs_eq]
  ... = C * (R⁻¹) ^ n
      : by rw inv_mul_cancel_left₀ two_pi_pos.ne.symm,
  exact h₄,
end


theorem liouville₄ {f : ℂ → E} (h : differentiable ℂ f) {C : ℝ} (C_pos : 0 < C) (hC : ∀ z, ∥f z∥ ≤ C) (n : ℕ) (hn : 0 < n) :
  ∀ ε > 0, ∥cauchy_power_series f 0 1 n∥ ≤ ε :=
begin
  intros ε hε,
  let R : ℝ≥0 := ⟨max 1 (C * ε⁻¹), le_trans zero_le_one (le_max_left 1 (C * ε⁻¹))⟩,
  have hR : 1 ≤ R, by exact_mod_cast le_max_left 1 (C * ε⁻¹),
  have R_pos : (0 : ℝ) < R, by exact_mod_cast (lt_of_lt_of_le zero_lt_one hR),
  refine le_trans (liouville₃ h hC (lt_of_lt_of_le zero_lt_one hR) n) _,
  simp only [inv_pow₀],
  have h₁ : ((R : ℝ) ^ n)⁻¹ ≤ R⁻¹,
    from inv_le_inv_of_le R_pos (by simpa using pow_le_pow (nnreal.coe_mono hR) hn),
  have h₂ : (R : ℝ)⁻¹ ≤ C⁻¹ * ε,
  { rw ←inv_inv₀ ε, rw ←mul_inv₀, exact inv_le_inv_of_le (mul_pos C_pos (inv_pos.mpr hε)) (le_max_right 1 (↑C * ε⁻¹)) },
  have h₃ := calc
  C * ((↑R) ^ n)⁻¹ ≤ C * (↑R)⁻¹ : mul_le_mul_of_nonneg_left h₁ C_pos.le
  ...             ≤ C * (C⁻¹ * ε) : mul_le_mul_of_nonneg_left h₂ C_pos.le
  ...             = ε : mul_inv_cancel_left₀ (by simp [C_pos.ne.symm]) _,
  exact h₃,
end

example (x : E) (h : ∥x∥ = 0) : x = 0 := norm_eq_zero.mp h

theorem liouville₅ {f : ℂ → E} (h : differentiable ℂ f) {C : ℝ} (C_pos : 0 < C) (hC : ∀ z, ∥f z∥ ≤ C) (n : ℕ) (hn : 0 < n) :
  cauchy_power_series f 0 1 n = 0 :=
begin
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add _) (norm_nonneg _)),
  simpa using liouville₄ h C_pos hC n hn,
end
