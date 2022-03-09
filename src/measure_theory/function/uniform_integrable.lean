/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.function.convergence_in_measure

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which estabishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales most notably is used to
fomulate the martingale convergence theorem.

## Main definitions

* `measure_theory.unif_integrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted `s` is smaller than `ε` for all `i`.
* `measure_theory.uniform_integrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

# Main results

* `measure_theory.unif_integrable_fintype`: a finite sequence of Lp functions is uniformly
  integrable.
* `measure_theory.tendsto_Lp_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `measure_theory.tendsto_in_measure_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniform integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

variables {α β ι : Type*} {m : measurable_space α} {μ : measure α} [normed_group β]

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted on `s` is less than `ε`.

Uniform integrablility is also known as uniformly absolutely continuous integrals. -/
def unif_integrable {m : measurable_space α} (f : ι → α → β) (p : ℝ≥0∞) (μ : measure α) : Prop :=
∀ ⦃ε : ℝ⦄ (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ i s, measurable_set s → μ s ≤ ennreal.of_real δ →
snorm (s.indicator (f i)) p μ ≤ ennreal.of_real ε

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α} [measurable_space β]
  (f : ι → α → β) (p : ℝ≥0∞) (μ : measure α) : Prop :=
(∀ i, measurable (f i)) ∧ unif_integrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, snorm (f i) p μ ≤ C

lemma uniform_integrable.measurable {mβ : measurable_space β} {f : ι → α → β} {p : ℝ≥0∞}
  (hf : uniform_integrable f p μ) (i : ι) : measurable (f i) :=
hf.1 i

lemma uniform_integrable.unif_integrable {mβ : measurable_space β} {f : ι → α → β} {p : ℝ≥0∞}
  (hf : uniform_integrable f p μ) : unif_integrable f p μ :=
hf.2.1

lemma uniform_integrable.mem_ℒp {mβ : measurable_space β} {f : ι → α → β} {p : ℝ≥0∞}
  (hf : uniform_integrable f p μ) (i : ι) :
  mem_ℒp (f i) p μ :=
⟨(hf.1 i).ae_measurable, let ⟨_, _, hC⟩ := hf.2 in lt_of_le_of_lt (hC i) ennreal.coe_lt_top⟩

section unif_integrable

/-! ### `unif_integrable`

This section deals with uniform integrability in the measure theory sense. -/

namespace unif_integrable

variables {f g : ι → α → β} {p : ℝ≥0∞}

protected lemma add {mβ : measurable_space β} [opens_measurable_space β]
  (hf : unif_integrable f p μ) (hg : unif_integrable g p μ) (hp : 1 ≤ p)
  (hf_meas : ∀ i, ae_measurable (f i) μ) (hg_meas : ∀ i, ae_measurable (g i) μ) :
  unif_integrable (f + g) p μ :=
begin
  intros ε hε,
  have hε2 : 0 < ε / 2 := half_pos hε,
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2,
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2,
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, λ i s hs hμs, _⟩,
  simp_rw [pi.add_apply, indicator_add'],
  refine (snorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans _,
  have hε_halves : ennreal.of_real ε = ennreal.of_real (ε / 2) + ennreal.of_real (ε / 2),
    by rw [← ennreal.of_real_add hε2.le hε2.le, add_halves],
  rw hε_halves,
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ennreal.of_real_le_of_real (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ennreal.of_real_le_of_real (min_le_right _ _)))),
end

protected lemma neg (hf : unif_integrable f p μ) : unif_integrable (-f) p μ :=
by { simp_rw [unif_integrable, pi.neg_apply, indicator_neg', snorm_neg], exact hf, }

protected lemma sub {mβ : measurable_space β} [opens_measurable_space β] [has_measurable_neg β]
  (hf : unif_integrable f p μ) (hg : unif_integrable g p μ) (hp : 1 ≤ p)
  (hf_meas : ∀ i, ae_measurable (f i) μ) (hg_meas : ∀ i, ae_measurable (g i) μ) :
  unif_integrable (f - g) p μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg hp hf_meas (λ i, (hg_meas i).neg), }

protected lemma ae_eq (hf : unif_integrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
  unif_integrable g p μ :=
begin
  intros ε hε,
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε,
  refine ⟨δ, hδ_pos, λ n s hs hμs, (le_of_eq $ snorm_congr_ae _).trans (hfδ n s hs hμs)⟩,
  filter_upwards [hfg n] with x hx,
  simp_rw [indicator_apply, hx],
end

end unif_integrable

lemma unif_integrable_congr_ae {f g : ι → α → β} {p : ℝ≥0∞} (hfg : ∀ n, f n =ᵐ[μ] g n) :
  unif_integrable f p μ ↔ unif_integrable g p μ :=
⟨λ hf, hf.ae_eq hfg, λ hg, hg.ae_eq (λ n, (hfg n).symm)⟩

lemma tendsto_indicator_ge (f : α → β) (x : α):
  tendsto (λ M : ℕ, {x | (M : ℝ) ≤ ∥f x∥₊}.indicator f x) at_top (𝓝 0) :=
begin
  refine @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ (nat.ceil (∥f x∥₊ : ℝ) + 1) (λ n hn, _),
  rw indicator_of_not_mem,
  simp only [not_le, mem_set_of_eq],
  refine lt_of_le_of_lt (nat.le_ceil _) _,
  refine lt_of_lt_of_le (lt_add_one _) _,
  norm_cast,
  rwa [ge_iff_le, coe_nnnorm] at hn,
end

variables (μ) {p : ℝ≥0∞}

section

variables [measurable_space β] [borel_space β] [hβ : second_countable_topology β] {f : α → β}
include hβ

/-- This lemma is weaker than `measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`. -/
lemma mem_ℒp.integral_indicator_norm_ge_le
  (hf : mem_ℒp f 1 μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, ∫⁻ x, ∥{x | M ≤ ∥f x∥₊}.indicator f x∥₊ ∂μ ≤ ennreal.of_real ε :=
begin
  have htendsto : ∀ᵐ x ∂μ, tendsto (λ M : ℕ, {x | (M : ℝ) ≤ ∥f x∥₊}.indicator f x) at_top (𝓝 0) :=
    univ_mem' (id $ λ x, tendsto_indicator_ge f x),
  have hmeas : ∀ M : ℕ, ae_measurable ({x | (M : ℝ) ≤ ∥f x∥₊}.indicator f) μ,
  { cases hf,
    measurability },
  have hbound : has_finite_integral (λ x, ∥f x∥) μ,
  { rw mem_ℒp_one_iff_integrable at hf,
    exact hf.norm.2 },
  have := tendsto_lintegral_norm_of_dominated_convergence hmeas hbound _ htendsto,
  { rw ennreal.tendsto_at_top_zero at this,
    obtain ⟨M, hM⟩ := this (ennreal.of_real ε) (ennreal.of_real_pos.2 hε),
    simp only [true_and, ge_iff_le, zero_tsub, zero_le,
              sub_zero, zero_add, coe_nnnorm, mem_Icc] at hM,
    refine ⟨M, _⟩,
    convert hM M le_rfl,
    ext1 x,
    simp only [coe_nnnorm, ennreal.of_real_eq_coe_nnreal (norm_nonneg _)],
    refl },
  { refine λ n, univ_mem' (id $ λ x, _),
    by_cases hx : (n : ℝ) ≤ ∥f x∥,
    { dsimp,
      rwa indicator_of_mem },
    { dsimp,
      rw [indicator_of_not_mem, norm_zero],
      { exact norm_nonneg _ },
      { assumption } } }
end

/-- This lemma is superceded by `measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability. -/
lemma mem_ℒp.integral_indicator_norm_ge_nonneg_le_of_meas
  (hf : mem_ℒp f 1 μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, 0 ≤ M ∧ ∫⁻ x, ∥{x | M ≤ ∥f x∥₊}.indicator f x∥₊ ∂μ ≤ ennreal.of_real ε :=
let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le μ hmeas hε in ⟨max M 0, le_max_right _ _, by simpa⟩

lemma mem_ℒp.integral_indicator_norm_ge_nonneg_le
  (hf : mem_ℒp f 1 μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, 0 ≤ M ∧ ∫⁻ x, ∥{x | M ≤ ∥f x∥₊}.indicator f x∥₊ ∂μ ≤ ennreal.of_real ε :=
begin
  have hf_mk : mem_ℒp (hf.1.mk f) 1 μ := (mem_ℒp_congr_ae hf.1.ae_eq_mk).mp hf,
  obtain ⟨M, hM_pos, hfM⟩ := hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas μ
    hf.1.measurable_mk hε,
  refine ⟨M, hM_pos, (le_of_eq _).trans hfM⟩,
  refine lintegral_congr_ae _,
  filter_upwards [hf.1.ae_eq_mk] with x hx,
  simp only [indicator_apply, coe_nnnorm, mem_set_of_eq, ennreal.coe_eq_coe, hx.symm],
end

omit hβ

lemma mem_ℒp.snorm_ess_sup_indicator_norm_ge_eq_zero
  (hf : mem_ℒp f ∞ μ) (hmeas : measurable f) :
  ∃ M : ℝ, snorm_ess_sup ({x | M ≤ ∥f x∥₊}.indicator f) μ = 0 :=
begin
  have hbdd : snorm_ess_sup f μ < ∞ := hf.snorm_lt_top,
  refine ⟨(snorm f ∞ μ + 1).to_real, _⟩,
  rw snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict,
  have : μ.restrict {x : α | (snorm f ⊤ μ + 1).to_real ≤ ∥f x∥₊} = 0,
  { simp only [coe_nnnorm, snorm_exponent_top, measure.restrict_eq_zero],
    have : {x : α | (snorm_ess_sup f μ + 1).to_real ≤ ∥f x∥} ⊆
      {x : α | snorm_ess_sup f μ < ∥f x∥₊},
    { intros x hx,
      rw [mem_set_of_eq, ← ennreal.to_real_lt_to_real hbdd.ne ennreal.coe_lt_top.ne,
          ennreal.coe_to_real, coe_nnnorm],
      refine lt_of_lt_of_le _ hx,
      rw ennreal.to_real_lt_to_real hbdd.ne,
      { exact ennreal.lt_add_right hbdd.ne one_ne_zero },
      { exact (ennreal.add_lt_top.2 ⟨hbdd, ennreal.one_lt_top⟩).ne } },
    rw ← nonpos_iff_eq_zero,
    refine (measure_mono this).trans _,
    have hle := coe_nnnorm_ae_le_snorm_ess_sup f μ,
    simp_rw [ae_iff, not_le] at hle,
    exact nonpos_iff_eq_zero.2 hle },
  rw [this, snorm_ess_sup_measure_zero],
  exact measurable_set_le measurable_const hmeas.nnnorm.subtype_coe,
end

/- This lemma is slightly weaker than `measure_theory.mem_ℒp.snorm_indicator_norm_ge_pos_le` as the
latter provides `0 < M`. -/
lemma mem_ℒp.snorm_indicator_norm_ge_le
  (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, snorm ({x | M ≤ ∥f x∥₊}.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  by_cases hp_ne_zero : p = 0,
  { refine ⟨1, hp_ne_zero.symm ▸ _⟩,
    simp [snorm_exponent_zero] },
  by_cases hp_ne_top : p = ∞,
  { subst hp_ne_top,
    obtain ⟨M, hM⟩ := hf.snorm_ess_sup_indicator_norm_ge_eq_zero μ hmeas,
    refine ⟨M, _⟩,
    simp only [snorm_exponent_top, hM, zero_le] },
  obtain ⟨M, hM', hM⟩ := @mem_ℒp.integral_indicator_norm_ge_nonneg_le _ _ _ μ _ _ _ _
    (λ x, ∥f x∥^p.to_real) (hf.norm_rpow hp_ne_zero hp_ne_top) _
    (real.rpow_pos_of_pos hε p.to_real),
  refine ⟨M ^(1 / p.to_real), _⟩,
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top,
      ← ennreal.rpow_one (ennreal.of_real ε)],
  conv_rhs { rw ← mul_one_div_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm },
  rw [ennreal.rpow_mul,
      ennreal.rpow_le_rpow_iff (one_div_pos.2 $ ennreal.to_real_pos hp_ne_zero hp_ne_top),
      ennreal.of_real_rpow_of_pos hε],
  convert hM,
  ext1 x,
  rw [ennreal.coe_rpow_of_nonneg _ ennreal.to_real_nonneg,
      nnnorm_indicator_eq_indicator_nnnorm, nnnorm_indicator_eq_indicator_nnnorm],
  have hiff : M ^ (1 / p.to_real) ≤ ∥f x∥₊ ↔ M ≤ ∥∥f x∥ ^ p.to_real∥₊,
  { rw [coe_nnnorm, coe_nnnorm, real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
        ← real.rpow_le_rpow_iff hM' (real.rpow_nonneg_of_nonneg (norm_nonneg _) _)
        (one_div_pos.2 $ ennreal.to_real_pos hp_ne_zero hp_ne_top),
        ← real.rpow_mul (norm_nonneg _),
        mul_one_div_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm, real.rpow_one] },
  by_cases hx : x ∈ {x : α | M ^ (1 / p.to_real) ≤ ∥f x∥₊},
  { rw [set.indicator_of_mem hx,set.indicator_of_mem, real.nnnorm_of_nonneg], refl,
    change _ ≤ _,
    rwa ← hiff },
  { rw [set.indicator_of_not_mem hx, set.indicator_of_not_mem],
    { simp [(ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm] },
    { change ¬ _ ≤ _,
      rwa ← hiff } }
end

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
lemma mem_ℒp.snorm_indicator_norm_ge_pos_le
  (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, 0 < M ∧ snorm ({x | M ≤ ∥f x∥₊}.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  obtain ⟨M, hM⟩ := hf.snorm_indicator_norm_ge_le μ hmeas hε,
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    le_trans (snorm_mono (λ x, _)) hM⟩,
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm],
  refine indicator_le_indicator_of_subset (λ x hx, _) (λ x, norm_nonneg _) x,
  change max _ _ ≤ _ at hx, -- removing the `change` breaks the proof!
  exact (max_le_iff.1 hx).1,
end

end

lemma snorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞)
  {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hf : ∀ x, ∥f x∥ < M) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  by_cases hM : M ≤ 0,
  { refine ⟨1, zero_lt_one, λ s hs hμ, _⟩,
    rw (_ : f = 0),
    { simp [hε.le] },
    { ext x,
      rw [pi.zero_apply, ← norm_le_zero_iff],
      exact (lt_of_lt_of_le (hf x) hM).le } },
  rw not_le at hM,
  refine ⟨(ε / M) ^ p.to_real, real.rpow_pos_of_pos (div_pos hε hM) _, λ s hs hμ, _⟩,
  by_cases hp : p = 0,
  { simp [hp] },
  rw snorm_indicator_eq_snorm_restrict hs,
  have haebdd : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ M,
  { filter_upwards,
    exact (λ x, (hf x).le) },
  refine le_trans (snorm_le_of_ae_bound haebdd) _,
  rw [measure.restrict_apply measurable_set.univ, univ_inter,
    ← ennreal.le_div_iff_mul_le (or.inl _) (or.inl ennreal.of_real_ne_top)],
  { rw [← one_div, ennreal.rpow_one_div_le_iff (ennreal.to_real_pos hp hp_top)],
    refine le_trans hμ _,
    rw [← ennreal.of_real_rpow_of_pos (div_pos hε hM),
      ennreal.rpow_le_rpow_iff (ennreal.to_real_pos hp hp_top), ennreal.of_real_div_of_pos hM],
    exact le_rfl },
  { simpa only [ennreal.of_real_eq_zero, not_le, ne.def] },
end

section

variables [measurable_space β] [borel_space β] {f : α → β}

/-- Auxiliary lemma for `measure_theory.mem_ℒp.snorm_indicator_le`. -/
lemma mem_ℒp.snorm_indicator_le' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ 2 * ennreal.of_real ε :=
begin
  obtain ⟨M, hMpos, hM⟩ := hf.snorm_indicator_norm_ge_pos_le μ hmeas hε,
  obtain ⟨δ, hδpos, hδ⟩ := @snorm_indicator_le_of_bound _ _ _ μ _ _
    ({x | ∥f x∥ < M}.indicator f) hp_top _ hε M _,
  { refine ⟨δ, hδpos, λ s hs hμs, _⟩,
    rw (_ : f = {x : α | M ≤ ∥f x∥₊}.indicator f + {x : α | ∥f x∥ < M}.indicator f),
    { rw snorm_indicator_eq_snorm_restrict hs,
      refine le_trans (snorm_add_le _ _ hp_one) _,
      { exact measurable.ae_measurable (hmeas.indicator
        (measurable_set_le measurable_const hmeas.nnnorm.subtype_coe)) },
      { exact measurable.ae_measurable (hmeas.indicator
        (measurable_set_lt hmeas.nnnorm.subtype_coe measurable_const)) },
      { rw two_mul,
        refine add_le_add (le_trans (snorm_mono_measure _ measure.restrict_le_self) hM) _,
        rw ← snorm_indicator_eq_snorm_restrict hs,
        exact hδ s hs hμs } },
    { ext x,
      by_cases hx : M ≤ ∥f x∥,
      { rw [pi.add_apply, indicator_of_mem, indicator_of_not_mem, add_zero];
        simpa },
      { rw [pi.add_apply, indicator_of_not_mem, indicator_of_mem, zero_add];
        simpa using hx } } },
  { intros x,
    rw [norm_indicator_eq_indicator_norm, indicator_apply],
    split_ifs,
    exacts [h, hMpos] }
end

/-- This lemma is superceded by `measure_theory.mem_ℒp.snorm_indicator_le` which does not require
measurability on `f`. -/
lemma mem_ℒp.snorm_indicator_le_of_meas (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  obtain ⟨δ, hδpos, hδ⟩ := hf.snorm_indicator_le' μ hp_one hp_top hmeas (half_pos hε),
  refine ⟨δ, hδpos, λ s hs hμs, le_trans (hδ s hs hμs) _⟩,
  rw [ennreal.of_real_div_of_pos zero_lt_two, (by norm_num : ennreal.of_real 2 = 2),
    ennreal.mul_div_cancel'];
  norm_num,
end

lemma mem_ℒp.snorm_indicator_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  (hf : mem_ℒp f p μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  have hℒp := hf,
  obtain ⟨⟨f', hf', heq⟩, hnorm⟩ := hf,
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).snorm_indicator_le_of_meas μ hp_one hp_top hf' hε,
  refine ⟨δ, hδpos, λ s hs hμs, _⟩,
  convert hδ s hs hμs using 1,
  rw [snorm_indicator_eq_snorm_restrict hs, snorm_indicator_eq_snorm_restrict hs],
  refine snorm_congr_ae heq.restrict,
end

/-- A constant function is uniformly integrable. -/
lemma unif_integrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : mem_ℒp g p μ) :
  unif_integrable (λ n : ι, g) p μ :=
begin
  intros ε hε,
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.snorm_indicator_le μ hp hp_ne_top hε,
  exact ⟨δ, hδ_pos, λ i, hgδ⟩,
end

/-- A single function is uniformly integrable. -/
lemma unif_integrable_subsingleton [subsingleton ι]
  (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  intros ε hε,
  by_cases hι : nonempty ι,
  { cases hι with i,
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).snorm_indicator_le μ hp_one hp_top hε,
    refine ⟨δ, hδpos, λ j s hs hμs, _⟩,
    convert hδ s hs hμs },
  { exact ⟨1, zero_lt_one, λ i, false.elim $ hι $ nonempty.intro i⟩ }
end

/-- This lemma is less general than `measure_theory.unif_integrable_fintype` which applies to
all sequences indexed by a fintype. -/
lemma unif_integrable_fin (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  {n : ℕ} {f : fin n → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  revert f,
  induction n with n h,
  { exact (λ f hf, unif_integrable_subsingleton μ hp_one hp_top hf) },
  intros f hfLp ε hε,
  set g : fin n → α → β := λ k, f k with hg,
  have hgLp : ∀ i, mem_ℒp (g i) p μ := λ i, hfLp i,
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε,
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp n).snorm_indicator_le μ hp_one hp_top hε,
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, λ i s hs hμs, _⟩,
  by_cases hi : i.val < n,
  { rw (_ : f i = g ⟨i.val, hi⟩),
    { exact hδ₁ _ s hs (le_trans hμs $ ennreal.of_real_le_of_real $ min_le_left _ _) },
    { rw hg, simp } },
  { rw (_ : i = n),
    { exact hδ₂ _ hs (le_trans hμs $ ennreal.of_real_le_of_real $ min_le_right _ _) },
    { have hi' := fin.is_lt i,
      rw nat.lt_succ_iff at hi',
      rw not_lt at hi,
      simp [← le_antisymm hi' hi] } }
end

/-- A finite sequence of Lp functions is uniformly integrable. -/
lemma unif_integrable_fintype [fintype ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  intros ε hε,
  set g : fin (fintype.card ι) → α → β := f ∘ (fintype.equiv_fin ι).symm,
  have hg : ∀ i, mem_ℒp (g i) p μ := λ _, hf _,
  obtain ⟨δ, hδpos, hδ⟩ := unif_integrable_fin μ hp_one hp_top hg hε,
  exact ⟨δ, hδpos, λ i s hs hμs,
    equiv.symm_apply_apply (fintype.equiv_fin ι) i ▸ hδ (fintype.equiv_fin ι i) s hs hμs⟩,
end

end

lemma snorm_sub_le_of_dist_bdd
  {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {s : set α} (hs : measurable_set[m] s)
  {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
  snorm (s.indicator (f - g)) p μ ≤ ennreal.of_real c * μ s ^ (1 / p.to_real) :=
begin
  have : ∀ x, ∥s.indicator (f - g) x∥ ≤ ∥s.indicator (λ x, c) x∥,
  { intro x,
    by_cases hx : x ∈ s,
    { rw [indicator_of_mem hx, indicator_of_mem hx, pi.sub_apply, ← dist_eq_norm,
          real.norm_eq_abs, abs_of_nonneg hc],
      exact hf x hx },
    { simp [indicator_of_not_mem hx] } },
  refine le_trans (snorm_mono this) _,
  rw snorm_indicator_const hs hp hp',
  refine ennreal.mul_le_mul (le_of_eq _) le_rfl,
  rw [← of_real_norm_eq_coe_nnnorm, real.norm_eq_abs, abs_of_nonneg hc],
end

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
lemma tendsto_Lp_of_tendsto_ae_of_meas {mβ : measurable_space β}
  [borel_space β] [second_countable_topology β] [is_finite_measure μ]
  (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hg' : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top_zero,
  intros ε hε,
  by_cases ε < ∞, swap,
  { rw [not_lt, top_le_iff] at h,
    exact ⟨0, λ n hn, by simp [h]⟩ },
  by_cases hμ : μ = 0,
  { exact ⟨0, λ n hn, by simp [hμ]⟩ },
  have hε' : 0 < ε.to_real / 3 :=
    div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (by norm_num),
  have hdivp : 0 ≤ 1 / p.to_real,
  { refine one_div_nonneg.2 _,
    rw [← ennreal.zero_to_real, ennreal.to_real_le_to_real ennreal.zero_ne_top hp'],
    exact le_trans ennreal.zero_lt_one.le hp },
  have hpow : 0 < (measure_univ_nnreal μ) ^ (1 / p.to_real) :=
    real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _,
  obtain ⟨δ₁, hδ₁, hsnorm₁⟩ := hui hε',
  obtain ⟨δ₂, hδ₂, hsnorm₂⟩ := hg'.snorm_indicator_le μ hp hp' hε',
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂),
  rw metric.tendsto_uniformly_on_iff at ht₂,
  specialize ht₂ (ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))
    (div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by norm_num) hpow)),
  obtain ⟨N, hN⟩ := eventually_at_top.1 ht₂, clear ht₂,
  refine ⟨N, λ n hn, _⟩,
  rw [← t.indicator_self_add_compl (f n - g)],
  refine le_trans (snorm_add_le ((((hf n).sub hg).indicator htm).ae_measurable)
    (((hf n).sub hg).indicator htm.compl).ae_measurable hp) _,
  rw [sub_eq_add_neg, indicator_add' t, indicator_neg'],
  refine le_trans (add_le_add_right (snorm_add_le ((hf n).indicator htm).ae_measurable
    (hg.indicator htm).neg.ae_measurable hp) _) _,
  have hnf : snorm (t.indicator (f n)) p μ ≤ ennreal.of_real (ε.to_real / 3),
  { refine hsnorm₁ n t htm (le_trans ht₁ _),
    rw ennreal.of_real_le_of_real_iff hδ₁.le,
    exact min_le_left _ _ },
  have hng : snorm (t.indicator g) p μ ≤ ennreal.of_real (ε.to_real / 3),
  { refine hsnorm₂ t htm (le_trans ht₁ _),
    rw ennreal.of_real_le_of_real_iff hδ₂.le,
    exact min_le_right _ _ },
  have hlt : snorm (tᶜ.indicator (f n - g)) p μ ≤ ennreal.of_real (ε.to_real / 3),
  { specialize hN n hn,
    have := snorm_sub_le_of_dist_bdd μ ((lt_of_lt_of_le ennreal.zero_lt_one hp).ne.symm)
      hp' htm.compl _ (λ x hx, (dist_comm (g x) (f n x) ▸ (hN x hx).le :
      dist (f n x) (g x) ≤ ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))),
    refine le_trans this _,
    rw [div_mul_eq_div_mul_one_div, ← ennreal.of_real_to_real (measure_lt_top μ tᶜ).ne,
        ennreal.of_real_rpow_of_nonneg ennreal.to_real_nonneg hdivp, ← ennreal.of_real_mul,
        mul_assoc],
    { refine ennreal.of_real_le_of_real (mul_le_of_le_one_right hε'.le _),
      rw [mul_comm, mul_one_div, div_le_one],
      { refine real.rpow_le_rpow ennreal.to_real_nonneg
          (ennreal.to_real_le_of_le_of_real (measure_univ_nnreal_pos hμ).le _) hdivp,
        rw [ennreal.of_real_coe_nnreal, coe_measure_univ_nnreal],
        exact measure_mono (subset_univ _) },
      { exact real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _ } },
    { refine mul_nonneg (hε').le (one_div_nonneg.2 hpow.le) },
    { rw div_mul_eq_div_mul_one_div,
      exact mul_nonneg hε'.le (one_div_nonneg.2 hpow.le) } },
  have : ennreal.of_real (ε.to_real / 3) = ε / 3,
  { rw [ennreal.of_real_div_of_pos (show (0 : ℝ) < 3, by norm_num), ennreal.of_real_to_real h.ne],
    simp },
  rw this at hnf hng hlt,
  rw [snorm_neg, ← ennreal.add_thirds ε, ← sub_eq_add_neg],
  exact add_le_add_three hnf hng hlt
end

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
lemma tendsto_Lp_of_tendsto_ae {mβ : measurable_space β}
  [borel_space β] [second_countable_topology β] [is_finite_measure μ]
  (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, ae_measurable (f n) μ) (hg : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  suffices : tendsto (λ (n : ℕ), snorm ((hf n).mk (f n) - (hg.1.mk g)) p μ) at_top (𝓝 0),
  { convert this,
    exact funext (λ n, snorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)), },
  refine tendsto_Lp_of_tendsto_ae_of_meas μ hp hp' (λ n, (hf n).measurable_mk) hg.1.measurable_mk
    (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq (λ n, (hf n).ae_eq_mk)) _,
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x,
  { rw ae_all_iff,
    exact λ n, (hf n).ae_eq_mk, },
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq,
  rw ← hxg_eq,
  convert hx_tendsto,
  ext1 n,
  exact (hxf_eq n).symm,
end

variables {mβ : measurable_space β} [borel_space β]
variables {f : ℕ → α → β} {g : α → β}

include mβ

lemma unif_integrable_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞)
  (hf : ∀ n, mem_ℒp (f n) p μ) (hf_tendsto : tendsto (λ n, snorm (f n) p μ) at_top (𝓝 0)) :
  unif_integrable f p μ :=
begin
  intros ε hε,
  rw ennreal.tendsto_at_top_zero at hf_tendsto,
  obtain ⟨N, hN⟩ := hf_tendsto (ennreal.of_real ε) (by simpa),
  set F : fin N → α → β := λ n, f n,
  have hF : ∀ n, mem_ℒp (F n) p μ := λ n, hf n,
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unif_integrable_fin μ hp hp' hF hε,
  refine ⟨δ₁, hδpos₁, λ n s hs hμs, _⟩,
  by_cases hn : n < N,
  { exact hδ₁ ⟨n, hn⟩ s hs hμs },
  { exact (snorm_indicator_le _).trans (hN n (not_lt.1 hn)) },
end

variables [second_countable_topology β]

/-- Convergence in Lp implies uniform integrability. -/
lemma unif_integrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  unif_integrable f p μ :=
begin
  have : f = (λ n, g) + λ n, f n - g, by { ext1 n, simp, },
  rw this,
  refine unif_integrable.add _ _ hp (λ _, hg.ae_measurable) (λ n, (hf n).1.sub hg.ae_measurable),
  { exact unif_integrable_const μ hp hp' hg, },
  { exact unif_integrable_of_tendsto_Lp_zero μ hp hp' (λ n, (hf n).sub hg) hfg, },
end

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
lemma tendsto_Lp_of_tendsto_in_measure [is_finite_measure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
  (hf : ∀ n, ae_measurable (f n) μ)
  (hg : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : tendsto_in_measure μ f at_top g) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  refine tendsto_of_subseq_tendsto (λ ns hns, _),
  obtain ⟨ms, hms, hms'⟩ := tendsto_in_measure.exists_seq_tendsto_ae (λ ε hε, (hfg ε hε).comp hns),
  exact ⟨ms, tendsto_Lp_of_tendsto_ae μ hp hp' (λ _, hf _) hg
    (λ ε hε, let ⟨δ, hδ, hδ'⟩ := hui hε in ⟨δ, hδ, λ i s hs hμs, hδ' _ s hs hμs⟩) hms'⟩,
end

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
lemma tendsto_in_measure_iff_tendsto_Lp [is_finite_measure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ) :
  tendsto_in_measure μ f at_top g ∧ unif_integrable f p μ ↔
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
⟨λ h, tendsto_Lp_of_tendsto_in_measure μ hp hp' (λ n, (hf n).1) hg h.2 h.1,
  λ h, ⟨tendsto_in_measure_of_tendsto_snorm
    (lt_of_lt_of_le ennreal.zero_lt_one hp).ne.symm
    (λ n, (hf n).ae_measurable)
    hg.ae_measurable h, unif_integrable_of_tendsto_Lp μ hp hp' hf hg h⟩⟩

end unif_integrable

end measure_theory
