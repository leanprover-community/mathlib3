import analysis.complex.cauchy_integral

variables
{E : Type*} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
[topological_space.second_countable_topology E] [complete_space E]


open real interval_integral
open_locale ennreal nnreal real

theorem differentiable.has_fpower_series_on_ball_top {f : ℂ → E} (h : differentiable ℂ f) (z : ℂ) {R : ℝ≥0} (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f z R) z ∞ :=
{ r_le :=
  begin
    refine top_le_iff.mpr (ennreal.eq_top_of_forall_nnreal_le (λ r, _)),
    by_cases hr : 0 < r,
    { exact ((h.differentiable_on.has_fpower_series_on_ball hR).exchange_radius
        (h.differentiable_on.has_fpower_series_on_ball hr)).r_le, },
    { exact le_trans (ennreal.coe_mono (not_lt.mp hr)) (by simp only [ennreal.coe_zero, zero_le]) },
  end,
  r_pos := dec_trivial,
  has_sum := λ y hy, let hy' := lt_of_le_of_lt (zero_le _) (lt_add_one ∥y∥₊) in
    ((h.differentiable_on.has_fpower_series_on_ball hR).exchange_radius
      (h.differentiable_on.has_fpower_series_on_ball hy')).has_sum
      (mem_emetric_ball_zero_iff.mpr (by exact_mod_cast (lt_add_one ∥y∥₊))) }

theorem differentiable.const_of_bounded {f : ℂ → E} (h : differentiable ℂ f) {C : ℝ} (C_pos : 0 < C) (hC : ∀ z, ∥f z∥ ≤ C) :
  f = (λ z, f 0) :=
begin
  have H₁ : ∀ {R : ℝ≥0} (hR : 0 < R) (n : ℕ), ∥cauchy_power_series f 0 1 n∥ ≤ C * (R⁻¹) ^ n,
  { intros R hR n,
    have h₁ : cauchy_power_series f 0 1 = cauchy_power_series f 0 R,
    from has_fpower_series_at.eq_formal_multilinear_series
      ((h.differentiable_on.has_fpower_series_on_ball zero_lt_one).has_fpower_series_at)
      ((h.differentiable_on.has_fpower_series_on_ball hR).has_fpower_series_at),
    calc ∥cauchy_power_series f 0 1 n∥
        ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map 0 R θ)∥) * (|R|⁻¹) ^ n
        : by simpa only [h₁] using norm_cauchy_power_series_le f 0 R n
    ... ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, C) * (|R|⁻¹) ^ n
        : mul_le_mul_of_nonneg_right ((mul_le_mul_left (inv_pos.mpr two_pi_pos)).mpr
            (integral_mono two_pi_pos.le h.continuous.norm.continuous_on.circle_integrable'
            (by simp) (λ θ, hC _))) (by simp)
    ... = (2 * π)⁻¹ * (2 * π * C) * (R⁻¹) ^ n
        : by simp only [integral_const, sub_zero, algebra.id.smul_eq_mul, nnreal.abs_eq]
    ... = C * (R⁻¹) ^ n
        : by rw inv_mul_cancel_left₀ two_pi_pos.ne.symm, },
  have H₂ : ∀ n > 0, ∀ ε > 0, ∃ {R : ℝ≥0}, 0 < R ∧ (R : ℝ)⁻¹ ^ n ≤ ε,
  { intros n hn ε hε,
    let R : ℝ≥0 := ⟨max 1 ε⁻¹, le_trans zero_le_one (le_max_left 1 ε⁻¹)⟩,
    have hR : 1 ≤ R, by exact_mod_cast le_max_left 1 ε⁻¹,
    have R_pos : (0 : ℝ) < R, by exact_mod_cast (lt_of_lt_of_le zero_lt_one hR),
    refine ⟨R, R_pos, _⟩,
    calc (R : ℝ)⁻¹ ^ n
        = ((↑R) ^ n)⁻¹ : inv_pow₀ _ _
    ... ≤ (↑R)⁻¹       : inv_le_inv_of_le R_pos (by simpa using pow_le_pow (nnreal.coe_mono hR) hn)
    ... ≤ ε            : inv_inv₀ ε ▸ inv_le_inv_of_le (inv_pos.mpr hε) (le_max_right 1 ε⁻¹), },
  have H₃ : ∀ n > 0, cauchy_power_series f 0 1 n = 0,
  { refine λ n hn, norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg _)),
    obtain ⟨R, hR, hRε⟩ := H₂ n hn (C⁻¹ * ε) (mul_pos (inv_pos.mpr C_pos) hε),
    calc ∥cauchy_power_series f 0 1 n∥ ≤ C * R⁻¹ ^ n : H₁ hR n
    ... ≤ C * (C⁻¹ * ε) : mul_le_mul_of_nonneg_left hRε C_pos.le
    ... = 0 + ε             : by simpa using mul_inv_cancel_left₀ C_pos.ne.symm _, },
  ext z,
  have H₄ := h.has_fpower_series_on_ball_top 0 zero_lt_one,
  have H₅ := (H₄.has_sum (mem_emetric_ball_zero_iff.mpr (@ennreal.coe_lt_top ∥z∥₊))).tsum_eq,
  calc f z = ∑' (b : ℕ), (cauchy_power_series f 0 1 b) (λ i, z)
           : by simpa only [zero_add] using H₅.symm
  ...      = (cauchy_power_series f 0 1 0) (λ i, z)
           : tsum_eq_single 0 (λ n hn, (by simp [H₃ n (zero_lt_iff.mpr hn)]))
  ...      = f 0
           : H₄.coeff_zero (λ i, z),
end
