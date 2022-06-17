/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.notation
import analysis.special_functions.integrals

/-!

# Tail probability

The tail probability formula states: if `X` is a nonnegative random variable, then
$$\mathbb{E}[X^p] = p \int_0^\infty t^{p - 1} \mathbb{P}(X \ge t) \lambda(dt).$$

## Main statement

* `measure_theory.integral_pow_nonneg_eq_integral_meas_le`: tail probability formula

-/

open_locale probability_theory nnreal ennreal

namespace measure_theory

open measure_space topological_space

variables {α : Type*} [measurable_space α] {μ : measure α} {X : α → ℝ} {p : ℕ}

lemma measurable_set_prod_Icc : measurable_set {x : ℝ × ℝ | x.1 ∈ set.Icc 0 x.2} :=
begin
  rw (_ : {x : ℝ × ℝ | x.fst ∈ set.Icc 0 x.snd} =
    (λ x : ℝ × ℝ, x.1) ⁻¹' (set.Ici 0) ∩ (λ x : ℝ × ℝ, x.2 - x.1) ⁻¹' (set.Ici 0)),
  { refine (measurable_fst measurable_set_Ici).inter
    ((measurable_snd.sub measurable_fst) measurable_set_Ici) },
  { ext, simp },
end

lemma integral_pow_nonneg_eq_integral_Ici_pow
  (hX : 0 ≤ X) (hm : measurable X) (hint : integrable (X ^ p) μ) :
  μ[X ^ p] = ∫ (x : ℝ) in set.Ici 0, x ^ p ∂measure.map X μ :=
begin
  have hint' : integrable_on (λ (x : ℝ), x ^ p) (set.Iio 0) (measure.map X μ),
  { refine integrable.integrable_on ((integrable_map_measure _ hm.ae_measurable).2 hint),
    measurability },
  rw (_ : ∫ ω, (X ^ p) ω ∂μ = ∫ x, x ^ p ∂(μ.map X)),
  { have hres : (measure.map X μ).restrict (set.Iio 0) = 0,
    { rw [measure.restrict_eq_zero, measure.map_apply hm measurable_set_Iio,
        (_ : X ⁻¹' set.Iio 0 = ∅), measure_empty],
      ext x,
      simpa using hX x },
    have : ∫ x in set.Iio 0, x ^ p ∂measure.map X μ = 0,
    { rw set_integral_eq_zero_iff_of_nonneg_ae _ hint',
      all_goals { simp only [hres, ae_zero] } },
    conv_rhs { rw ← add_zero (∫ (x : ℝ) in set.Ici 0, x ^ p ∂measure.map X μ),
      congr,
      skip,
      rw ← this },
    rw [← integral_union _ measurable_set_Iio _ hint', set.union_comm, set.Iio_union_Ici,
      measure.restrict_univ],
    { rintro x ⟨hx₁, hx₂⟩,
      rw set.mem_Iio at hx₂,
      exact not_le.2 hx₂ hx₁ },
    { refine integrable.integrable_on ((integrable_map_measure _ hm.ae_measurable).2 hint),
      measurability } },
  { rw integral_map hm.ae_measurable,
    { refl },
    { measurability } },
end

-- rw using moments once #14755 is merged

/-- **Tail probability** (tail sum formula): the `p`-th moment of a non-negative random variable is
equal to `p * ∫ t in set.Ici 0, t ^ (p - 1) * (μ {ω | t ≤ X ω}).to_real`. We obtain the usual
formula in the case that `p = 1`. -/
theorem integral_pow_nonneg_eq_integral_meas_le [is_finite_measure μ]
  (hp : 0 < p) (hX : 0 ≤ X) (hm : measurable X) (hint : integrable (X ^ p) μ) :
  μ[X ^ p] = p * ∫ t in set.Ici 0, t ^ (p - 1) * (μ {ω | t ≤ X ω}).to_real :=
begin
  have hμ : ∫ t in set.Ici 0, t ^ (p - 1) * (μ {ω | t ≤ X ω}).to_real =
    ∫ t in set.Ici 0, t ^ (p - 1) *
      ∫ x in set.Ici 0, (set.Icc 0 x).indicator (1 : ℝ → ℝ) t ∂(μ.map X),
  { refine set_integral_congr measurable_set_Ici (λ t ht, _),
    rw set.mem_Ici at ht,
    simp only [mul_eq_mul_left_iff],
    have : ∀ x : ℝ, (set.Icc 0 x).indicator (1 : ℝ → ℝ) t = (set.Ici t).indicator 1 x,
    { intro x,
      by_cases t ∈ set.Icc 0 x,
      { rw [set.indicator_of_mem h, set.indicator_of_mem, pi.one_apply, pi.one_apply],
        exact h.2 },
      { rw [set.indicator_of_not_mem h, set.indicator_of_not_mem],
        exact λ h', h ⟨ht, h'⟩ } },
    left,
    simp only [this, set_integral_indicator measurable_set_Ici, set.Ici_inter_Ici, pi.one_apply,
      integral_const, measure.restrict_apply', measurable_set_Ici, set.univ_inter,
      smul_eq_mul, mul_one, measure.map_apply hm measurable_set_Ici, sup_eq_right.2 ht],
    refl },
  simp_rw [hμ, integral_pow_nonneg_eq_integral_Ici_pow hX hm hint,
    ← integral_mul_pow_eq_pow p hp,
    interval_integral.integral_const_mul, integral_mul_left],
  congr' 1,
  simp_rw ← integral_mul_left,
  change _ = ∫ t in set.Ici (0 : ℝ), ∫ x in set.Ici 0,
    (λ t : ℝ × ℝ, t.1 ^ (p - 1) * (set.Icc (0 : ℝ) t.2).indicator 1 t.1) ⟨t, x⟩ ∂(μ.map X),
  rw [integral_integral_swap],
  { refine set_integral_congr measurable_set_Ici (λ t ht, _),
    simp_rw [← smul_eq_mul, ← set.indicator_const_smul_apply, pi.one_apply, smul_eq_mul, mul_one,
      interval_integral.integral_of_le ht, set_integral_indicator' measurable_set_Icc,
      ← integral_Icc_eq_integral_Ioc],
    congr,
    ext,
    simp only [set.mem_Icc, set.mem_inter_eq, set.mem_Ici, and_self_left]},
  { change integrable (λ t : ℝ × ℝ, t.1 ^ (p - 1) * (set.Icc (0 : ℝ) t.2).indicator 1 t.1) _,
    rw integrable_prod_iff',
    { refine ⟨filter.eventually_of_forall (λ x, _), _⟩,
      { simp_rw [function.uncurry_apply_pair, ← smul_eq_mul, ← set.indicator_const_smul_apply],
        refine (integrable_indicator_iff measurable_set_Icc).2
          (integrable_on.restrict (continuous.integrable_on_Icc
          ((continuous_pow (p - 1)).smul _)) measurable_set_Icc),
        simp only [pi.one_apply, continuous_const] },
      { have h₁ : ∀ y : ℝ, ∫ x : ℝ in set.Ici 0, (set.Icc 0 y).indicator (λ _, ∥x ^ (p - 1)∥) x
          = ∫ x : ℝ in set.Ici 0 ∩ set.Icc 0 y, ∥x ^ (p - 1)∥,
        { intro y,
          exact set_integral_indicator' measurable_set_Icc _ },
        have h₂ : ∀ y : ℝ, ∫ x : ℝ in set.Ici 0 ∩ set.Icc 0 y, ∥x ^ (p - 1)∥ =
          (set.Ici (0 : ℝ)).indicator (λ _, (p : ℝ)⁻¹ * y ^ p) y,
        { intro y,
          rw (_ : set.Ici 0 ∩ set.Icc 0 y = set.Icc 0 y),
          by_cases hy : 0 ≤ y,
          { rw [integral_Icc_eq_integral_Ioc, ← interval_integral.integral_of_le hy,
              set.indicator_of_mem,
              (by rw nat.sub_add_cancel (nat.succ_le_iff.2 hp) : p = p - 1 + 1),
              (by norm_cast : (↑(p - 1 + 1) : ℝ) = ↑(p - 1) + 1), ← integral_pow' (p - 1)],
            { refine interval_integral.integral_congr (λ x hx, _),
              obtain ⟨hx, -⟩ := hx,
              rw min_eq_left hy at hx,
              simp only [nat.add_succ_sub_one, add_zero, norm_pow, real.norm_of_nonneg hx] },
            { exact hy } },
          { rw [set.Icc_eq_empty hy, integral_empty, set.indicator_of_not_mem],
            exact hy },
          { ext,
            simp only [set.mem_inter_eq, set.mem_Ici, set.mem_Icc, and_self_left] } },
        simp_rw [function.uncurry_apply_pair, ← smul_eq_mul, ← set.indicator_const_smul_apply,
          norm_indicator_eq_indicator_norm, pi.one_apply, smul_eq_mul, mul_one, h₁, h₂],
        refine integrable.integrable_on ((integrable_map_measure _ hm.ae_measurable).2
          ((hint.const_mul _).indicator (hm measurable_set_Ici))),
        { refine measurable.ae_strongly_measurable
            (((measurable_id'.pow_const _).const_mul _).indicator measurable_set_Ici) } } },
    { refine ((measurable_fst.pow measurable_const).mul
        (measurable.indicator _ measurable_set_prod_Icc)).ae_strongly_measurable,
      simp only [pi.one_apply, measurable_const] } }
end

end measure_theory
