import probability.notation
import measure_theory.integral.interval_integral

/-
Tail probability states: if `X` is a nonnegative random variable, then
$$\mathbb{E}[X^p] = p \int_0^\infty t^{p - 1} \mathbb{P}(X \ge t) \lambda(dt).$$
-/

open_locale probability_theory nnreal ennreal

namespace measure_theory

open measure_space

variables {α : Type*} [measurable_space α] {μ : measure α}
  {X : α → ℝ} {p : ℕ}

lemma intervale_integrabl_mul_pow_eq_pow (hp : 0 < p) (x : ℝ) :
  ∫ t in 0..x, ↑p * t ^ (p - 1) = x ^ p :=
begin
  have : deriv (λ t, t ^ p) = (λ t : ℝ, ↑p * t ^ (p - 1)),
  { ext x, rw deriv_pow },
  rw [interval_integral.integral_deriv_eq_sub' _ this _
    (continuous_const.mul (continuous_pow (p - 1))).continuous_on],
  { simp only [zero_pow hp, sub_zero] },
  { rintro t ht,
    simp only [differentiable_at.pow, differentiable_at_id'] },
end

lemma aux (x : ℝ) :
  (set.Ici (0 : ℝ)).eq_on
  (λ t, (set.Icc 0 x).indicator (1 : ℝ → ℝ) t)
  (λ t, (set.Ici t).indicator (1 : ℝ → ℝ) x) :=
begin
  classical,
  intros t hnonneg,
  simp only,
  by_cases ht : t ∈ set.Icc 0 x,
  { rw [set.indicator_apply, set.indicator_apply, if_pos ht, if_pos],
    { refl },
    { exact ht.2 } },
  { rw [set.indicator_apply, set.indicator_apply, if_neg ht, if_neg],
    simp only [*, set.mem_Ici, not_le, set.mem_Icc, not_and, set.mem_set_of_eq] at * }
end

lemma set_integral_indicator {E : Type*} [normed_group E] [normed_space ℝ E]
  [complete_space E] {s t : set α} (ht : measurable_set t) (f : α → E) :
  ∫ x in s, t.indicator f x ∂μ = ∫ x in s ∩ t, f x ∂μ :=
by rw [integral_indicator ht, measure.restrict_restrict ht, set.inter_comm]

lemma set_integral_indicator' {E : Type*} [normed_group E] [normed_space ℝ E]
  [complete_space E] {s t : set α} (ht : measurable_set t) (f : α → α → E) :
  ∫ x in s, t.indicator (f x) x ∂μ = ∫ x in s ∩ t, f x x ∂μ :=
sorry

lemma set.eq_on_of_eq (s : set ℝ) {f g : ℝ → ℝ} (hf : f = g) : s.eq_on f g :=
by rw hf

-- rw using moments once #14755 is merged
theorem foo [is_finite_measure μ] (hp : 0 < p) (hX : 0 ≤ X) (hm : measurable X) :
  μ[X ^ p] = p * ∫ t in set.Ici 0, t ^ (p - 1) * (μ {ω | t ≤ X ω}).to_real :=
begin
  have hinteq : ∫ ω, (X ^ p) ω ∂μ = ∫ x in set.Ici 0, x ^ p ∂(μ.map X), sorry,
  -- { rw integral_map hm.ae_measurable,
  --   { refl },
  --   { measurability } },
  have hμ : ∫ t in set.Ici 0, t ^ (p - 1) * (μ {ω | t ≤ X ω}).to_real =
    ∫ t in set.Ici 0, t ^ (p - 1) *
      ∫ x in set.Ici 0, (set.Icc 0 x).indicator (1 : ℝ → ℝ) t ∂(μ.map X),
  { sorry },
  simp_rw [hμ, hinteq, ← intervale_integrabl_mul_pow_eq_pow hp,
    interval_integral.integral_const_mul, integral_mul_left],
  congr' 1,
  simp_rw ← integral_mul_left,
  change _ = ∫ t in set.Ici (0 : ℝ), ∫ x in set.Ici 0,
    (λ t : ℝ × ℝ, t.1 ^ (p - 1) * (set.Icc (0 : ℝ) t.2).indicator 1 t.1) ⟨t, x⟩ ∂(μ.map X),
  rw [integral_integral_swap],
  { simp only,
    refine set_integral_congr measurable_set_Ici (λ t ht, _),
    simp_rw [← smul_eq_mul, ← set.indicator_const_smul_apply, pi.one_apply, smul_eq_mul, mul_one,
      interval_integral.integral_of_le ht, set_integral_indicator' measurable_set_Icc,
      ← integral_Icc_eq_integral_Ioc],
    congr,
    ext,
    simp },
  sorry,
end

end measure_theory
