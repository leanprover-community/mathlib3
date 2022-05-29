/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals

/-!
# The layer cake formula, a.k.a. Cavalieri's principle

In this file we prove the layer cake formula using Fubini's theorem.

## Main definitions

None.

## Main results

* `layercake`

## Tags

layer cake theorem, Cavalieri's principle
-/

noncomputable theory
open_locale classical topological_space ennreal measure_theory
open set function real ennreal
open measure_theory measurable_space measure_theory.measure
open topological_space
open filter

/-! ### Layercake theorem -/
section layercake

variables {α : Type*} [measurable_space α] {f g : α → ℝ} {s : set α}

theorem layercake_of_measurable
  (μ : measure α) [sigma_finite μ]
  {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : measurable f)
  {g : ℝ → ℝ} (g_intble : ∀ t > 0, interval_integrable g volume 0 t)
  (g_mble : measurable g) (g_nn : ∀ t > 0, 0 ≤ g t) :
  ∫⁻ ω, ennreal.of_real (∫ t in 0 .. (f ω), g t) ∂μ
    = ∫⁻ t, (μ {a : α | t ≤ f a}) * ennreal.of_real (g t) ∂(volume.restrict (Ioi 0)) :=
begin
  have integrand_eq : ∀ ω, ennreal.of_real (∫ t in 0 .. (f ω), g t)
        = ∫⁻ t, ennreal.of_real (g t) ∂(volume.restrict (Ioc 0 (f ω))),
  { intro ω,
    by_cases f ω = 0, by simp [h],
    have f_pos : 0 < f ω, from lt_of_le_of_ne (f_nn ω) (ne_comm.mp h),
    have intble_now := g_intble (f ω) f_pos,
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g,
    { filter_upwards [self_mem_ae_restrict
                      (show measurable_set (Ioc 0 (f ω)), from measurable_set_Ioc)],
      exact λ x hx, g_nn x hx.1, },
    rw ← of_real_integral_eq_lintegral_of_real intble_now.1 g_ae_nn,
    apply congr_arg,
    rw interval_integral.interval_integral_eq_integral_interval_oc,
    simp only [interval_oc_of_le, (show (0 ≤ f ω), from f_nn ω), if_true,
               algebra.id.smul_eq_mul, one_mul], },
  simp_rw [integrand_eq, ← lintegral_indicator (λ t, ennreal.of_real (g t)) measurable_set_Ioc],
  simp_rw [← lintegral_indicator _ measurable_set_Ioi],
  rw lintegral_lintegral_swap,
  { apply congr_arg,
    funext s,
    have : (λ (x : α), (Ioc 0 (f x)).indicator (λ (t : ℝ), ennreal.of_real (g t)) s)
            = (λ (x : α), (ennreal.of_real (g s) * (Ioi (0 : ℝ)).indicator (λ _, 1) s)
                          * (Ici s).indicator (λ (t : ℝ), (1 : ℝ≥0∞)) (f x)),
    { funext a,
      by_cases s ∈ Ioc (0 : ℝ) (f a),
      { simp only [h, (show s ∈ Ioi (0 : ℝ), from h.1),
                    (show f a ∈ Ici s, from h.2), indicator_of_mem, mul_one], },
      { simp only [mem_Ioc, not_and, not_le] at h,
        by_cases h' : 0 < s,
        { simp only [(show s ∉ Ioc 0 (f a), by simpa only [mem_Ioc, not_and, not_le] using h),
                     indicator_of_not_mem, not_false_iff, zero_eq_mul, mul_eq_zero,
                     ennreal.of_real_eq_zero, indicator_apply_eq_zero, mem_Ioi,
                     one_ne_zero, mem_Ici],
          right,
          intro con,
          specialize h h',
          rw ← not_lt at con,
          contradiction, },
        { simp at h',
          have : s ∉ Ioi (0 : ℝ), by simp only [h', mem_Ioi, not_lt],
          simp only [this, indicator_of_not_mem, not_false_iff, mul_zero,
                    zero_mul, indicator_apply_eq_zero, mem_Ioc, ennreal.of_real_eq_zero, and_imp],
          intros con,
          contradiction, }, }, },
    simp_rw this,
    rw lintegral_const_mul',
    swap, { apply ennreal.mul_ne_top ennreal.of_real_ne_top,
            by_cases s ∈ Ioi (0 : ℝ); { simp [h], }, },
    have aux : (λ a, (Ici s).indicator (λ (t : ℝ), (1 : ℝ≥0∞)) (f a))
              = (λ a, {a : α | s ≤ f a}.indicator (λ _, 1) a),
    { funext a,
      by_cases s ≤ f a; simp [h], },
    simp_rw [aux],
    rw lintegral_indicator, swap, { exact f_mble measurable_set_Ici, },
    rw lintegral_one,
    simp only [measure.restrict_apply, measurable_set.univ, univ_inter],
    rw indicator_mul_left,
    rw mul_assoc,
    have whee : (Ioi 0).indicator (λ (_x : ℝ), (1 : ℝ≥0∞)) s * μ {a : α | s ≤ f a}
                = (Ioi 0).indicator (λ (_x : ℝ), 1 * μ {a : α | s ≤ f a}) s,
    { by_cases 0 < s; simp [h], },
    rw whee,
    rw mul_comm _ (ennreal.of_real _),
    simp_rw [one_mul],
    refl, },
  have : function.uncurry
         (λ (x : α) (y : ℝ), (Ioc 0 (f x)).indicator (λ (t : ℝ), ennreal.of_real (g t)) y)
           = {p : α × ℝ | p.2 ∈ Ioc 0 (f p.1)}.indicator (λ p, ennreal.of_real (g p.2)),
  { funext p,
    by_cases p.2 ∈ Ioc 0 (f p.1),
    { have h' : p ∈ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)}, by simpa only using h,
      rw set.indicator_of_mem h',
      cases p,
      dsimp,
      simp only [h, indicator_of_mem], },
    { have h' : p ∉ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)}, by simpa only using h,
      rw set.indicator_of_not_mem h',
      cases p,
      dsimp,
      rw set.indicator_of_not_mem h, }, },
  rw this,
  have mble := measurable_set_region_between_oc measurable_zero f_mble measurable_set.univ,
  simp only [mem_univ, pi.zero_apply, true_and] at mble,
  apply (ae_measurable_indicator_iff mble).mpr,
  apply measurable.ae_measurable,
  apply ennreal.measurable_of_real.comp,
  exact g_mble.comp measurable_snd,
end

theorem layercake (μ : measure α) [sigma_finite μ]
  {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : measurable f)
  {g : ℝ → ℝ} (g_intble : ∀ t > 0, interval_integrable g volume 0 t)
  (g_nn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ g t) :
  ∫⁻ ω, ennreal.of_real (∫ t in 0 .. (f ω), g t) ∂μ
    = ∫⁻ t, (μ {a : α | t ≤ f a}) * ennreal.of_real (g t) ∂(volume.restrict (Ioi 0)) :=
begin
  have ex_G : ∃ (G : ℝ → ℝ),
              measurable G ∧ g =ᵐ[volume.restrict (Ioi (0 : ℝ))] G ∧ 0 ≤ G,
  { suffices : ∃ (G : ℝ → ℝ), measurable G ∧ g =ᵐ[volume.restrict (Ioi (0 : ℝ))] G,
    { rcases this with ⟨G₁, mble_G₁, g_eq_G₁⟩,
      use (λ a, max 0 (G₁ a)),
      refine ⟨measurable.max measurable_const mble_G₁, _, _⟩,
      { filter_upwards [g_nn, g_eq_G₁],
        intros a ga_nn ga_eq,
        simp only [←ga_eq, ga_nn, max_eq_right], },
      { exact λ a, by simp only [pi.zero_apply, le_max_iff, le_refl, true_or], }, },
    suffices : ae_measurable g (volume.restrict (Ioi (0 : ℝ))), from this,
    have Ioi_eq_Union : Ioi (0 : ℝ) = ⋃ (n : ℕ), Ioc 0 (n : ℝ),
    { rw Union_Ioc_eq_Ioi_self_iff.mpr,
      intros x x_pos,
      exact exists_nat_ge x, },
    rw [Ioi_eq_Union, ae_measurable_Union_iff],
    intros n,
    by_cases n = 0,
    { simp only [h, nat.cast_zero, Ioc_self,
                 measure.restrict_empty, _root_.ae_measurable_zero_measure], },
    { exact (g_intble n (nat.cast_pos.mpr (zero_lt_iff.mpr h))).1.1.ae_measurable, }, },
  rcases ex_G with ⟨G, ⟨G_mble, g_eq_G, G_nn⟩⟩,
  have g_eq_G_on : ∀ (t : ℝ), g =ᵐ[volume.restrict (Ioc 0 t)] G,
  from λ t, ae_mono (measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G,
  have G_nn' : ∀ t > 0, 0 ≤ G t, from λ t t_pos, G_nn t,
  have G_intble : ∀ t > 0, interval_integrable G volume 0 t,
  { intros t t_pos,
    refine ⟨integrable_on.congr_fun' (g_intble t t_pos).1 (g_eq_G_on t), _⟩,
    convert integrable_on_empty,
    exact Ioc_eq_empty_of_le (show 0 ≤ t, by linarith), },
  have eq₁ : ∫⁻ (t : ℝ) in Ioi 0, μ {a : α | t ≤ f a} * ennreal.of_real (g t)
             = ∫⁻ (t : ℝ) in Ioi 0, μ {a : α | t ≤ f a} * ennreal.of_real (G t),
  { apply lintegral_congr_ae,
    filter_upwards [g_eq_G],
    intros a ha,
    rw [ha], },
  have eq₂ : ∀ ω, ∫ (t : ℝ) in 0..f ω, g t = ∫ (t : ℝ) in 0..f ω, G t,
  { intro ω,
    have fω_nn : 0 ≤ f ω, by simpa only using f_nn ω,
    rw [interval_integral.integral_of_le fω_nn, interval_integral.integral_of_le fω_nn],
    exact integral_congr_ae (g_eq_G_on (f ω)), },
  rw eq₁,
  simp_rw eq₂,
  exact layercake_of_measurable μ f_nn f_mble G_intble G_mble (λ t t_pos, G_nn t),
end

theorem layercake_one
  (μ : measure α) [sigma_finite μ]
  {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : measurable f) :
  ∫⁻ ω, ennreal.of_real (f ω) ∂μ = ∫⁻ t in Ioi 0, (μ {a : α | t ≤ f a}) :=
begin
  set cst := λ (t : ℝ), (1 : ℝ) with def_cst,
  have cst_intble : ∀ t > 0, interval_integrable cst volume 0 t,
  from λ _ _, interval_integrable_const,
  have key := layercake μ f_nn f_mble cst_intble (eventually_of_forall (λ t, zero_le_one)),
  simp_rw [def_cst, ennreal.of_real_one, mul_one] at key,
  rw ← key,
  apply congr_arg,
  funext ω,
  simp only [interval_integral.integral_const, sub_zero, algebra.id.smul_eq_mul, mul_one],
end

-- TODO: Lean gets stuck if I try with `(p_large : 0 < p)` instead... Why?
theorem layercake_p
  (μ : measure α) [sigma_finite μ]
  {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : measurable f) {p : ℝ}
  (p_large : 1 < p) :
  ∫⁻ ω, ennreal.of_real ((f ω)^p) ∂μ
    = (ennreal.of_real p) * ∫⁻ t in Ioi 0, (μ {a : α | t ≤ f a}) * ennreal.of_real (t^(p-1)) :=
begin
  have p_pos : 0 < p := by linarith,
  have obs : ∀ (x : ℝ), (∫ (t : ℝ) in 0..x, t^(p-1)) = x^p / p,
  { intros x,
    rw integral_rpow (or.inl (show 0 ≤ p - 1, by linarith)),
    simp [real.zero_rpow p_pos.ne.symm], },
  set g := λ (t : ℝ), t^(p-1) with g_def,
  have g_nn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ g t,
  { filter_upwards [self_mem_ae_restrict
                    (show measurable_set (Ioi (0 : ℝ)), from measurable_set_Ioi)],
    intros t t_pos,
    rw g_def,
    apply real.rpow_nonneg_of_nonneg (mem_Ioi.mp t_pos).le, },
  have g_intble : ∀ t > 0, interval_integrable g volume 0 t,
  from λ _ _, interval_integral.interval_integrable_rpow (or.inl (show 0 ≤ p - 1, by linarith)),
  have key := layercake μ f_nn f_mble g_intble g_nn,
  simp_rw [g_def] at key,
  rw [← key, ← lintegral_const_mul (ennreal.of_real p)]; simp_rw obs,
  { apply congr_arg,
    funext ω,
    rw [← ennreal.of_real_mul p_pos.le, mul_div_cancel' ((f ω)^p) p_pos.ne.symm], },
  { apply ennreal.measurable_of_real.comp,
    apply (measurable_div_const' p).comp,
    have : measurable (λ (z : ℝ), z^p),
    { apply continuous.measurable,
      exact continuous.rpow_const continuous_id (λ _, (or.inr p_pos.le)), },
    apply this.comp f_mble, },
end

end layercake
