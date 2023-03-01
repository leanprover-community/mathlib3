/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara
-/
import measure_theory.integral.set_integral
import probability.independence

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `measurable_space` `M2` to define `μ`:

```lean
example {M1 : measurable_space Ω} [M2 : measurable_space Ω] {μ : measure Ω} : sorry := sorry
example [M1 : measurable_space Ω] {M2 : measurable_space Ω} {μ : measure Ω} : sorry := sorry
```

-/

noncomputable theory
open set measure_theory
open_locale ennreal measure_theory

variables {Ω : Type*} {mΩ : measurable_space Ω} {μ : measure Ω} {f g : Ω → ℝ≥0∞} {X Y : Ω → ℝ}

namespace probability_theory

/-- If a random variable `f` in `ℝ≥0∞` is independent of an event `T`, then if you restrict the
  random variable to `T`, then `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
  `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space`. -/
lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : measurable_space Ω}
  {μ : measure Ω} (hMf : Mf ≤ mΩ) (c : ℝ≥0∞) {T : set Ω} (h_meas_T : measurable_set T)
  (h_ind : indep_sets {s | measurable_set[Mf] s} {T} μ) (h_meas_f : measurable[Mf] f) :
  ∫⁻ ω, f ω * T.indicator (λ _, c) ω ∂μ = ∫⁻ ω, f ω ∂μ * ∫⁻ ω, T.indicator (λ _, c) ω ∂μ :=
begin
  revert f,
  have h_mul_indicator : ∀ g, measurable g → measurable (λ a, g a * T.indicator (λ x, c) a),
    from λ g h_mg, h_mg.mul (measurable_const.indicator h_meas_T),
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
    simp_rw [← inter_indicator_mul],
    rw [lintegral_indicator _ (measurable_set.inter (hMf _ h_meas_s') (h_meas_T)),
      lintegral_indicator _ (hMf _ h_meas_s'), lintegral_indicator _ h_meas_T],
    simp only [measurable_const, lintegral_const, univ_inter, lintegral_const_mul,
      measurable_set.univ, measure.restrict_apply],
    ring_nf,
    congr,
    rw [mul_comm, h_ind s' T h_meas_s' (set.mem_singleton _)], },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' : measurable f', from h_meas_f'.mono hMf le_rfl,
    have h_measM_g : measurable g, from h_meas_g.mono hMf le_rfl,
    simp_rw [pi.add_apply, right_distrib],
    rw [lintegral_add_left (h_mul_indicator _ h_measM_f'),
      lintegral_add_left h_measM_f', right_distrib, h_ind_f', h_ind_g] },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f : ∀ n, measurable (f n), from λ n, (h_meas_f n).mono hMf le_rfl,
    simp_rw [ennreal.supr_mul],
    rw [lintegral_supr h_measM_f h_mono_f, lintegral_supr, ennreal.supr_mul],
    { simp_rw [← h_ind_f] },
    { exact λ n, h_mul_indicator _ (h_measM_f n) },
    { exact λ m n h_le a, mul_le_mul_right' (h_mono_f h_le a) _, }, },
end

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  {Mf Mg mΩ : measurable_space Ω} {μ : measure Ω}
  (hMf : Mf ≤ mΩ) (hMg : Mg ≤ mΩ) (h_ind : indep Mf Mg μ)
  (h_meas_f : measurable[Mf] f) (h_meas_g : measurable[Mg] g) :
  ∫⁻ ω, f ω * g ω ∂μ = ∫⁻ ω, f ω ∂μ * ∫⁻ ω, g ω ∂μ :=
begin
  revert g,
  have h_measM_f : measurable f, from h_meas_f.mono hMf le_rfl,
  apply measurable.ennreal_induction,
  { intros c s h_s,
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f,
    apply indep_sets_of_indep_sets_of_le_right h_ind,
    rwa singleton_subset_iff, },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' : measurable f', from h_measMg_f'.mono hMg le_rfl,
    have h_measM_g : measurable g, from h_measMg_g.mono hMg le_rfl,
    simp_rw [pi.add_apply, left_distrib],
    rw [lintegral_add_left h_measM_f', lintegral_add_left (h_measM_f.mul h_measM_f'),
      left_distrib, h_ind_f', h_ind_g'] },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' : ∀ n, measurable (f' n), from λ n, (h_meas_f' n).mono hMg le_rfl,
    simp_rw [ennreal.mul_supr],
    rw [lintegral_supr, lintegral_supr h_measM_f' h_mono_f', ennreal.mul_supr],
    { simp_rw [← h_ind_f'], },
    { exact λ n, h_measM_f.mul (h_measM_f' n), },
    { exact λ n m (h_le : n ≤ m) a, mul_le_mul_left' (h_mono_f' h_le a) _, }, }
end

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
   then `E[f * g] = E[f] * E[g]`. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
  (h_meas_f : measurable f) (h_meas_g : measurable g) (h_indep_fun : indep_fun f g μ) :
  ∫⁻ ω, (f * g) ω ∂μ = ∫⁻ ω, f ω ∂μ * ∫⁻ ω, g ω ∂μ :=
lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
  (measurable.of_comap_le le_rfl) (measurable.of_comap_le le_rfl)

/-- If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measurable,
   then `E[f * g] = E[f] * E[g]` (slightly generalizing
   `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun`). -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'
  (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ) (h_indep_fun : indep_fun f g μ) :
  ∫⁻ ω, (f * g) ω ∂μ = ∫⁻ ω, f ω ∂μ * ∫⁻ ω, g ω ∂μ :=
begin
  have fg_ae : f * g =ᵐ[μ] (h_meas_f.mk _) * (h_meas_g.mk _),
    from h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk,
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk, lintegral_congr_ae h_meas_g.ae_eq_mk,
    lintegral_congr_ae fg_ae],
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
    h_meas_f.measurable_mk h_meas_g.measurable_mk,
  exact h_indep_fun.ae_eq h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk
end

lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun''
  (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ) (h_indep_fun : indep_fun f g μ) :
  ∫⁻ ω, f ω * g ω ∂μ = ∫⁻ ω, f ω ∂μ * ∫⁻ ω, g ω ∂μ :=
lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' h_meas_f h_meas_g h_indep_fun

/-- The product of two independent, integrable, real_valued random variables is integrable. -/
lemma indep_fun.integrable_mul {β : Type*} [measurable_space β] {X Y : Ω → β}
  [normed_division_ring β] [borel_space β]
  (hXY : indep_fun X Y μ) (hX : integrable X μ) (hY : integrable Y μ) :
  integrable (X * Y) μ :=
begin
  let nX : Ω → ennreal := λ a, ‖X a‖₊,
  let nY : Ω → ennreal := λ a, ‖Y a‖₊,

  have hXY' : indep_fun (λ a, ‖X a‖₊) (λ a, ‖Y a‖₊) μ :=
    hXY.comp measurable_nnnorm measurable_nnnorm,
  have hXY'' : indep_fun nX nY μ :=
    hXY'.comp measurable_coe_nnreal_ennreal measurable_coe_nnreal_ennreal,

  have hnX : ae_measurable nX μ := hX.1.ae_measurable.nnnorm.coe_nnreal_ennreal,
  have hnY : ae_measurable nY μ := hY.1.ae_measurable.nnnorm.coe_nnreal_ennreal,

  have hmul : ∫⁻ a, nX a * nY a ∂μ = ∫⁻ a, nX a ∂μ * ∫⁻ a, nY a ∂μ :=
    by convert lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' hnX hnY hXY'',

  refine ⟨hX.1.mul hY.1, _⟩,
  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul, hmul],
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hX.2, hY.2⟩)
end

/-- If the product of two independent real_valued random variables is integrable and
the second one is not almost everywhere zero, then the first one is integrable. -/
lemma indep_fun.integrable_left_of_integrable_mul {β : Type*} [measurable_space β] {X Y : Ω → β}
  [normed_division_ring β] [borel_space β]
  (hXY : indep_fun X Y μ) (h'XY : integrable (X * Y) μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) (h'Y : ¬(Y =ᵐ[μ] 0)) :
  integrable X μ :=
begin
  refine ⟨hX, _⟩,
  have I : ∫⁻ ω, ‖Y ω‖₊ ∂μ ≠ 0,
  { assume H,
    have I : (λ ω, ↑‖Y ω‖₊) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.ennnorm).1 H,
    apply h'Y,
    filter_upwards [I] with ω hω,
    simpa using hω },
  apply lt_top_iff_ne_top.2 (λ H, _),
  have J : indep_fun (λ ω, ↑‖X ω‖₊) (λ ω, ↑‖Y ω‖₊) μ,
  { have M : measurable (λ (x : β), (‖x‖₊ : ℝ≥0∞)) := measurable_nnnorm.coe_nnreal_ennreal,
    apply indep_fun.comp hXY M M },
  have A : ∫⁻ ω, ‖X ω * Y ω‖₊ ∂μ < ∞ := h'XY.2,
  simp only [nnnorm_mul, ennreal.coe_mul] at A,
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'' hX.ennnorm hY.ennnorm J, H] at A,
  simpa [ennreal.top_mul, I] using A,
end

/-- If the product of two independent real_valued random variables is integrable and the
first one is not almost everywhere zero, then the second one is integrable. -/
lemma indep_fun.integrable_right_of_integrable_mul {β : Type*} [measurable_space β] {X Y : Ω → β}
  [normed_division_ring β] [borel_space β]
  (hXY : indep_fun X Y μ) (h'XY : integrable (X * Y) μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) (h'X : ¬(X =ᵐ[μ] 0)) :
  integrable Y μ :=
begin
  refine ⟨hY, _⟩,
  have I : ∫⁻ ω, ‖X ω‖₊ ∂μ ≠ 0,
  { assume H,
    have I : (λ ω, ↑‖X ω‖₊) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hX.ennnorm).1 H,
    apply h'X,
    filter_upwards [I] with ω hω,
    simpa using hω },
  apply lt_top_iff_ne_top.2 (λ H, _),
  have J : indep_fun (λ ω, ↑‖X ω‖₊) (λ ω, ↑‖Y ω‖₊) μ,
  { have M : measurable (λ (x : β), (‖x‖₊ : ℝ≥0∞)) := measurable_nnnorm.coe_nnreal_ennreal,
    apply indep_fun.comp hXY M M },
  have A : ∫⁻ ω, ‖X ω * Y ω‖₊ ∂μ < ∞ := h'XY.2,
  simp only [nnnorm_mul, ennreal.coe_mul] at A,
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'' hX.ennnorm hY.ennnorm J, H] at A,
  simpa [ennreal.top_mul, I] using A,
end

/-- The (Bochner) integral of the product of two independent, nonnegative random
  variables is the product of their integrals. The proof is just plumbing around
  `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'`. -/
lemma indep_fun.integral_mul_of_nonneg (hXY : indep_fun X Y μ) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
  (hXm : ae_measurable X μ) (hYm : ae_measurable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  have h1 : ae_measurable (λ a, ennreal.of_real (X a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hXm,
  have h2 : ae_measurable (λ a, ennreal.of_real (Y a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hYm,
  have h3 : ae_measurable (X * Y) μ := hXm.mul hYm,

  have h4 : 0 ≤ᵐ[μ] (X * Y) := ae_of_all _ (λ ω, mul_nonneg (hXp ω) (hYp ω)),

  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hXp) hXm.ae_strongly_measurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hYp) hYm.ae_strongly_measurable,
    integral_eq_lintegral_of_nonneg_ae h4 h3.ae_strongly_measurable],
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXp _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' h1 h2,
  exact hXY.comp ennreal.measurable_of_real ennreal.measurable_of_real
end

/-- The (Bochner) integral of the product of two independent, integrable random
  variables is the product of their integrals. The proof is pedestrian decomposition
  into their positive and negative parts in order to apply `indep_fun.integral_mul_of_nonneg`
  four times. -/
theorem indep_fun.integral_mul_of_integrable (hXY : indep_fun X Y μ)
  (hX : integrable X μ) (hY : integrable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  let pos : ℝ → ℝ := (λ x, max x 0),
  let neg : ℝ → ℝ := (λ x, max (-x) 0),
  have posm : measurable pos := measurable_id'.max measurable_const,
  have negm : measurable neg := measurable_id'.neg.max measurable_const,

  let Xp := pos ∘ X, -- `X⁺` would look better but it makes `simp_rw` below fail
  let Xm := neg ∘ X,
  let Yp := pos ∘ Y,
  let Ym := neg ∘ Y,

  have hXpm : X = Xp - Xm := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (X ω)).symm),
  have hYpm : Y = Yp - Ym := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm),

  have hp1 : 0 ≤ Xm := λ ω, le_max_right _ _,
  have hp2 : 0 ≤ Xp := λ ω, le_max_right _ _,
  have hp3 : 0 ≤ Ym := λ ω, le_max_right _ _,
  have hp4 : 0 ≤ Yp := λ ω, le_max_right _ _,

  have hm1 : ae_measurable Xm μ := hX.1.ae_measurable.neg.max ae_measurable_const,
  have hm2 : ae_measurable Xp μ := hX.1.ae_measurable.max ae_measurable_const,
  have hm3 : ae_measurable Ym μ := hY.1.ae_measurable.neg.max ae_measurable_const,
  have hm4 : ae_measurable Yp μ := hY.1.ae_measurable.max ae_measurable_const,

  have hv1 : integrable Xm μ := hX.neg_part,
  have hv2 : integrable Xp μ := hX.pos_part,
  have hv3 : integrable Ym μ := hY.neg_part,
  have hv4 : integrable Yp μ := hY.pos_part,

  have hi1 : indep_fun Xm Ym μ := hXY.comp negm negm,
  have hi2 : indep_fun Xp Ym μ := hXY.comp posm negm,
  have hi3 : indep_fun Xm Yp μ := hXY.comp negm posm,
  have hi4 : indep_fun Xp Yp μ := hXY.comp posm posm,

  have hl1 : integrable (Xm * Ym) μ := hi1.integrable_mul hv1 hv3,
  have hl2 : integrable (Xp * Ym) μ := hi2.integrable_mul hv2 hv3,
  have hl3 : integrable (Xm * Yp) μ := hi3.integrable_mul hv1 hv4,
  have hl4 : integrable (Xp * Yp) μ := hi4.integrable_mul hv2 hv4,
  have hl5 : integrable (Xp * Yp - Xm * Yp) μ := hl4.sub hl3,
  have hl6 : integrable (Xp * Ym - Xm * Ym) μ := hl2.sub hl1,

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  rw [integral_sub' hl5 hl6, integral_sub' hl4 hl3, integral_sub' hl2 hl1,
    integral_sub' hv2 hv1, integral_sub' hv4 hv3, hi1.integral_mul_of_nonneg hp1 hp3 hm1 hm3,
    hi2.integral_mul_of_nonneg hp2 hp3 hm2 hm3, hi3.integral_mul_of_nonneg hp1 hp4 hm1 hm4,
    hi4.integral_mul_of_nonneg hp2 hp4 hm2 hm4],
  ring
end

/-- The (Bochner) integral of the product of two independent random
  variables is the product of their integrals. -/
theorem indep_fun.integral_mul (hXY : indep_fun X Y μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  by_cases h'X : X =ᵐ[μ] 0,
  { have h' : X * Y =ᵐ[μ] 0,
    { filter_upwards [h'X] with ω hω,
      simp [hω] },
    simp only [integral_congr_ae h'X, integral_congr_ae h', pi.zero_apply, integral_const,
      algebra.id.smul_eq_mul, mul_zero, zero_mul] },
  by_cases h'Y : Y =ᵐ[μ] 0,
  { have h' : X * Y =ᵐ[μ] 0,
    { filter_upwards [h'Y] with ω hω,
      simp [hω] },
    simp only [integral_congr_ae h'Y, integral_congr_ae h', pi.zero_apply, integral_const,
      algebra.id.smul_eq_mul, mul_zero, zero_mul] },
  by_cases h : integrable (X * Y) μ,
  { have HX : integrable X μ := hXY.integrable_left_of_integrable_mul h hX hY h'Y,
    have HY : integrable Y μ := hXY.integrable_right_of_integrable_mul h hX hY h'X,
    exact hXY.integral_mul_of_integrable HX HY },
  { have I : ¬(integrable X μ ∧ integrable Y μ),
    { rintros ⟨HX, HY⟩,
      exact h (hXY.integrable_mul HX HY) },
    rw not_and_distrib at I,
    cases I;
    simp [integral_undef, I, h] }
end

theorem indep_fun.integral_mul' (hXY : indep_fun X Y μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) :
  integral μ (λ ω, X ω * Y ω) = integral μ X * integral μ Y :=
hXY.integral_mul hX hY

/-- Independence of functions `f` and `g` into arbitrary types is characterized by the relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` with values in `ℝ`
  satisfying appropriate integrability conditions. -/
theorem indep_fun_iff_integral_comp_mul [is_finite_measure μ]
  {β β' : Type*} {mβ : measurable_space β} {mβ' : measurable_space β'}
  {f : Ω → β} {g : Ω → β'} {hfm : measurable f} {hgm : measurable g} :
  indep_fun f g μ ↔
  ∀ {φ : β → ℝ} {ψ : β' → ℝ},
    measurable φ → measurable ψ → integrable (φ ∘ f) μ → integrable (ψ ∘ g) μ →
    integral μ ((φ ∘ f) * (ψ ∘ g)) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) :=
begin
  refine ⟨λ hfg _ _ hφ hψ, indep_fun.integral_mul_of_integrable (hfg.comp hφ hψ), _⟩,
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  specialize h (measurable_one.indicator hA) (measurable_one.indicator hB)
    ((integrable_const 1).indicator (hfm.comp measurable_id hA))
    ((integrable_const 1).indicator (hgm.comp measurable_id hB)),
  rwa [← ennreal.to_real_eq_to_real (measure_ne_top μ _), ennreal.to_real_mul,
    ← integral_indicator_one ((hfm hA).inter (hgm hB)), ← integral_indicator_one (hfm hA),
    ← integral_indicator_one (hgm hB), set.inter_indicator_one],
  exact ennreal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)
end

end probability_theory
