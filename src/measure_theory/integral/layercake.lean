/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

In this file we prove the following layer cake formula.

Consider a non-negative measurable function `f` on a sigma-finite measure space. Apply pointwise
to it an increasing absolutely continuous function `G : ℝ≥0 → ℝ≥0` vanishing at the origin, with
derivative `G' = g` on the positive real line (in other words, `G` a primitive of a non-negative
locally integrable function `g` on the positive real line). Then the integral of the result,
`∫ G ∘ f`, can be written as the integral over the positive real line of the "tail measures" of `f`
(i.e., a function giving the measures of the sets on which `f` exceeds different positive real
values) weighted by `g`. In probability theory contexts, the "tail measures" could be referred to
as "tail probabilities" of the random variable `f`, or as values of the "complementary cumulative
distribution function" of the random variable `f`. The terminology "tail probability formula" is
therefore occasionally used for the layer cake formula (or a standard application of it).

The essence of the (mathematical) proof is Fubini's theorem.

We also give the two most common applications of the layer cake formula
 * a representation of the integral of a nonnegative function f:
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt
 * a representation of the integral of the p:th power of a nonnegative function f:
   ∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt .

## Main results

 * `lintegral_comp_eq_lintegral_meas_le_mul`: The general layer cake formula with Lebesgue
   integrals.
 * `lintegral_eq_lintegral_meas_le`: The most common special case of the layer cake formula, which
   states that for a nonnegative function f we have ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt .

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

noncomputable theory
open_locale ennreal measure_theory
open set measure_theory filter

/-! ### Layercake theorem -/
section layercake

namespace measure_theory

variables {α : Type*} [measurable_space α] {f : α → ℝ} {g : ℝ → ℝ} {s : set α}

/-- An auxiliary version of the layer cake theorem (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions.

See `measure_theory.layercake` for the main formulation of the layer cake theorem. -/
lemma lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : measure α) [sigma_finite μ]
  (f_nn : 0 ≤ f) (f_mble : measurable f)
  (g_intble : ∀ t > 0, interval_integrable g volume 0 t)
  (g_mble : measurable g) (g_nn : ∀ t > 0, 0 ≤ g t) :
  ∫⁻ ω, ennreal.of_real (∫ t in 0 .. (f ω), g t) ∂μ
    = ∫⁻ t in Ioi 0, (μ {a : α | t ≤ f a}) * ennreal.of_real (g t) :=
begin
  have g_intble' : ∀ (t : ℝ), 0 ≤ t → interval_integrable g volume 0 t,
  { intros t ht,
    cases eq_or_lt_of_le ht,
    { simp [← h], },
    { exact g_intble t h, }, },
  have integrand_eq : ∀ ω, ennreal.of_real (∫ t in 0 .. (f ω), g t)
                           = ∫⁻ t in Ioc 0 (f ω), ennreal.of_real (g t),
  { intro ω,
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g,
    { filter_upwards [self_mem_ae_restrict (measurable_set_Ioc : measurable_set (Ioc 0 (f ω)))]
        with x hx using g_nn x hx.1, },
    rw ← of_real_integral_eq_lintegral_of_real (g_intble' (f ω) (f_nn ω)).1 g_ae_nn,
    congr,
    exact interval_integral.integral_of_le (f_nn ω), },
  simp_rw [integrand_eq, ← lintegral_indicator (λ t, ennreal.of_real (g t)) measurable_set_Ioc,
           ← lintegral_indicator _ measurable_set_Ioi],
  rw lintegral_lintegral_swap,
  { apply congr_arg,
    funext s,
    have aux₁ : (λ x, (Ioc 0 (f x)).indicator (λ (t : ℝ), ennreal.of_real (g t)) s)
                = (λ x, (ennreal.of_real (g s) * (Ioi (0 : ℝ)).indicator (λ _, 1) s)
                             * (Ici s).indicator (λ (t : ℝ), (1 : ℝ≥0∞)) (f x)),
    { funext a,
      by_cases s ∈ Ioc (0 : ℝ) (f a),
      { simp only [h, (show s ∈ Ioi (0 : ℝ), from h.1),
                   (show f a ∈ Ici s, from h.2), indicator_of_mem, mul_one], },
      { have h_copy := h,
        simp only [mem_Ioc, not_and, not_le] at h,
        by_cases h' : 0 < s,
        { simp only [h_copy, h h', indicator_of_not_mem, not_false_iff, mem_Ici, not_le,
                     mul_zero], },
        { have : s ∉ Ioi (0 : ℝ) := h',
          simp only [this, h', indicator_of_not_mem, not_false_iff, mul_zero, zero_mul, mem_Ioc,
                     false_and], }, }, },
    simp_rw aux₁,
    rw lintegral_const_mul',
    swap, { apply ennreal.mul_ne_top ennreal.of_real_ne_top,
            by_cases s ∈ Ioi (0 : ℝ); { simp [h], }, },
    simp_rw [(show (λ a, (Ici s).indicator (λ (t : ℝ), (1 : ℝ≥0∞)) (f a))
                   = (λ a, {a : α | s ≤ f a}.indicator (λ _, 1) a),
              by { funext a, by_cases s ≤ f a; simp [h], })],
    rw lintegral_indicator,
    swap, { exact f_mble measurable_set_Ici, },
    rw [lintegral_one, measure.restrict_apply measurable_set.univ, univ_inter, indicator_mul_left,
        mul_assoc,
        (show (Ioi 0).indicator (λ (_x : ℝ), (1 : ℝ≥0∞)) s * μ {a : α | s ≤ f a}
              = (Ioi 0).indicator (λ (_x : ℝ), 1 * μ {a : α | s ≤ f a}) s,
        by { by_cases 0 < s; simp [h], })],
    simp_rw [mul_comm _ (ennreal.of_real _), one_mul],
    refl, },
  have aux₂ : function.uncurry
              (λ (x : α) (y : ℝ), (Ioc 0 (f x)).indicator (λ (t : ℝ), ennreal.of_real (g t)) y)
              = {p : α × ℝ | p.2 ∈ Ioc 0 (f p.1)}.indicator (λ p, ennreal.of_real (g p.2)),
  { funext p,
    cases p,
    rw function.uncurry_apply_pair,
    by_cases p_snd ∈ Ioc 0 (f p_fst),
    { have h' : (p_fst, p_snd) ∈ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h,
      rw [set.indicator_of_mem h', set.indicator_of_mem h], },
    { have h' : (p_fst, p_snd) ∉ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h,
      rw [set.indicator_of_not_mem h', set.indicator_of_not_mem h], }, },
  rw aux₂,
  have mble := measurable_set_region_between_oc measurable_zero f_mble measurable_set.univ,
  simp_rw [mem_univ, pi.zero_apply, true_and] at mble,
  exact (ennreal.measurable_of_real.comp (g_mble.comp measurable_snd)).ae_measurable.indicator mble,
end

/-- The layer cake theorem / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0 .. ∞, g(t) * μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : measure α) [sigma_finite μ]
  (f_nn : 0 ≤ f) (f_mble : measurable f)
  (g_intble : ∀ t > 0, interval_integrable g volume 0 t)
  (g_nn : ∀ᵐ t ∂(volume.restrict (Ioi 0)), 0 ≤ g t) :
  ∫⁻ ω, ennreal.of_real (∫ t in 0 .. f ω, g t) ∂μ
    = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ennreal.of_real (g t) :=
begin
  have ex_G : ∃ (G : ℝ → ℝ), measurable G ∧ 0 ≤ G ∧ g =ᵐ[volume.restrict (Ioi 0)] G,
  { refine ae_measurable.exists_measurable_nonneg _ g_nn,
    exact ae_measurable_Ioi_of_forall_Ioc (λ t ht, (g_intble t ht).1.1.ae_measurable), },
  rcases ex_G with ⟨G, G_mble, G_nn, g_eq_G⟩,
  have g_eq_G_on : ∀ t, g =ᵐ[volume.restrict (Ioc 0 t)] G,
    from λ t, ae_mono (measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G,
  have G_intble : ∀ t > 0, interval_integrable G volume 0 t,
  { refine λ t t_pos, ⟨integrable_on.congr_fun' (g_intble t t_pos).1 (g_eq_G_on t), _⟩,
    rw Ioc_eq_empty_of_le t_pos.lt.le,
    exact integrable_on_empty, },
  have eq₁ : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ennreal.of_real (g t)
             = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ennreal.of_real (G t),
  { apply lintegral_congr_ae,
    filter_upwards [g_eq_G] with a ha,
    rw [ha], },
  have eq₂ : ∀ ω, ∫ t in 0..f ω, g t = ∫ t in 0..f ω, G t,
  { refine λ ω, interval_integral.integral_congr_ae _,
    have fω_nn : 0 ≤ f ω := f_nn ω,
    rw [interval_oc_of_le fω_nn,
        ← ae_restrict_iff' (measurable_set_Ioc : measurable_set (Ioc (0 : ℝ) (f ω)))],
    exact g_eq_G_on (f ω), },
  simp_rw [eq₁, eq₂],
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ f_nn f_mble
    G_intble G_mble (λ t t_pos, G_nn t),
end

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0 .. ∞, μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_eq_lintegral_meas_le (μ : measure α) [sigma_finite μ]
  (f_nn : 0 ≤ f) (f_mble : measurable f) :
  ∫⁻ ω, ennreal.of_real (f ω) ∂μ = ∫⁻ t in Ioi 0, (μ {a : α | t ≤ f a}) :=
begin
  set cst := λ (t : ℝ), (1 : ℝ) with def_cst,
  have cst_intble : ∀ t > 0, interval_integrable cst volume 0 t,
    from λ _ _, interval_integrable_const,
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble cst_intble
              (eventually_of_forall (λ t, zero_le_one)),
  simp_rw [def_cst, ennreal.of_real_one, mul_one] at key,
  rw ← key,
  congr' with ω,
  simp only [interval_integral.integral_const, sub_zero, algebra.id.smul_eq_mul, mul_one],
end

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0 .. ∞, t^(p-1) * μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_rpow_eq_lintegral_meas_le_mul (μ : measure α) [sigma_finite μ]
  (f_nn : 0 ≤ f) (f_mble : measurable f) {p : ℝ} (p_pos: 0 < p) :
  ∫⁻ ω, ennreal.of_real ((f ω)^p) ∂μ
    = (ennreal.of_real p) * ∫⁻ t in Ioi 0, (μ {a : α | t ≤ f a}) * ennreal.of_real (t^(p-1)) :=
begin
  have one_lt_p : -1 < p - 1 := by linarith,
  have obs : ∀ (x : ℝ), (∫ (t : ℝ) in 0..x, t^(p-1)) = x^p / p,
  { intros x,
    rw integral_rpow (or.inl one_lt_p),
    simp [real.zero_rpow p_pos.ne.symm], },
  set g := λ (t : ℝ), t^(p-1) with g_def,
  have g_nn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ g t,
  { filter_upwards [self_mem_ae_restrict (measurable_set_Ioi : measurable_set (Ioi (0 : ℝ)))],
    intros t t_pos,
    rw g_def,
    exact real.rpow_nonneg_of_nonneg (mem_Ioi.mp t_pos).le (p - 1), },
  have g_intble : ∀ t > 0, interval_integrable g volume 0 t,
    from λ _ _, interval_integral.interval_integrable_rpow' one_lt_p,
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn,
  simp_rw [g_def] at key,
  rw [← key, ← lintegral_const_mul (ennreal.of_real p)]; simp_rw obs,
  { congr' with ω,
    rw [← ennreal.of_real_mul p_pos.le, mul_div_cancel' ((f ω)^p) p_pos.ne.symm], },
  { exact ((f_mble.pow measurable_const).div_const p).ennreal_of_real, },
end

end measure_theory

end layercake
