/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import analysis.normed_space.dual
import measure_theory.function.strongly_measurable
import measure_theory.integral.set_integral

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite`: case of a sigma-finite measure.
* `ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq`: for functions which are
  `ae_fin_strongly_measurable`.
* `Lp.ae_eq_of_forall_set_integral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `integrable.ae_eq_of_forall_set_integral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_set_integral_eq_zero`.

We also register the corresponding lemma for integrals of `ℝ≥0∞`-valued functions, in
`ae_eq_of_forall_set_lintegral_eq_of_sigma_finite`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `λ x, inner c (f x) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the dual space, `λ x, c (f x) =ᵐ[μ] 0`
  then `f =ᵐ[μ] 0`.

-/

open measure_theory topological_space normed_space filter

open_locale ennreal nnreal measure_theory

namespace measure_theory


section ae_eq_of_forall

variables {α E 𝕜 : Type*} {m : measurable_space α} {μ : measure α} [is_R_or_C 𝕜]

lemma ae_eq_zero_of_forall_inner [inner_product_space 𝕜 E] [second_countable_topology E]
  {f : α → E} (hf : ∀ c : E, (λ x, (inner c (f x) : 𝕜)) =ᵐ[μ] 0) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq E,
  have hs : dense_range s := dense_range_dense_seq E,
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜), from ae_all_iff.mpr (λ n, hf (s n)),
  refine hf'.mono (λ x hx, _),
  rw [pi.zero_apply, ← inner_self_eq_zero],
  have h_closed : is_closed {c : E | inner c (f x) = (0 : 𝕜)},
    from is_closed_eq (continuous_id.inner continuous_const) continuous_const,
  exact @is_closed_property ℕ E _ s (λ c, inner c (f x) = (0 : 𝕜)) hs h_closed (λ n, hx n) _,
end

local notation `⟪`x`, `y`⟫` := y x

variables (𝕜)

lemma ae_eq_zero_of_forall_dual [normed_group E] [normed_space 𝕜 E]
  [second_countable_topology E]
  {f : α → E} (hf : ∀ c : dual 𝕜 E, (λ x, ⟪f x, c⟫) =ᵐ[μ] 0) :
  f =ᵐ[μ] 0 :=
begin
  let u := dense_seq E,
  have hu : dense_range u := dense_range_dense_seq _,
  have : ∀ n, ∃ g : E →L[𝕜] 𝕜, ∥g∥ ≤ 1 ∧ g (u n) = norm' 𝕜 (u n) :=
    λ n, exists_dual_vector'' 𝕜 (u n),
  choose s hs using this,
  have A : ∀ (a : E), (∀ n, ⟪a, s n⟫ = (0 : 𝕜)) → a = 0,
  { assume a ha,
    contrapose! ha,
    have a_pos : 0 < ∥a∥, by simp only [ha, norm_pos_iff, ne.def, not_false_iff],
    have a_mem : a ∈ closure (set.range u), by simp [hu.closure_range],
    obtain ⟨n, hn⟩ : ∃ (n : ℕ), dist a (u n) < ∥a∥ / 2 :=
      metric.mem_closure_range_iff.1 a_mem (∥a∥/2) (half_pos a_pos),
    use n,
    have I : ∥a∥/2 < ∥u n∥,
    { have : ∥a∥ ≤ ∥u n∥ + ∥a - u n∥ := norm_le_insert' _ _,
      have : ∥a - u n∥ < ∥a∥/2, by rwa dist_eq_norm at hn,
      linarith },
    assume h,
    apply lt_irrefl (∥s n (u n)∥),
    calc ∥s n (u n)∥ = ∥s n (u n - a)∥ : by simp only [h, sub_zero, continuous_linear_map.map_sub]
    ... ≤ 1 * ∥u n - a∥ : continuous_linear_map.le_of_op_norm_le _ (hs n).1 _
    ... < ∥a∥ / 2 : by { rw [one_mul], rwa dist_eq_norm' at hn }
    ... < ∥u n∥ : I
    ... = ∥s n (u n)∥ : by rw [(hs n).2, norm_norm'] },
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, ⟪f x, s n⟫ = (0 : 𝕜), from λ n, hf (s n),
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪f x, s n⟫ = (0 : 𝕜), by rwa ae_all_iff,
  exact hf'.mono (λ x hx, A (f x) hx),
end

variables {𝕜}

end ae_eq_of_forall


variables {α E : Type*}
  {m m0 : measurable_space α} {μ : measure α} {s t : set α}
  [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [second_countable_topology E]
  [complete_space E]
  {p : ℝ≥0∞}

section ae_eq_of_forall_set_integral_eq

lemma ae_const_le_iff_forall_lt_measure_zero {β} [linear_order β] [topological_space β]
  [order_topology β] [first_countable_topology β] (f : α → β) (c : β) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  split,
  { assume h b hb,
    exact measure_mono_null (λ y hy, (lt_of_le_of_lt hy hb : _)) h },
  assume hc,
  by_cases h : ∀ b, c ≤ b,
  { have : {a : α | f a < c} = ∅,
    { apply set.eq_empty_iff_forall_not_mem.2 (λ x hx, _),
      exact (lt_irrefl _ (lt_of_lt_of_le hx (h (f x)))).elim },
    simp [this] },
  by_cases H : ¬ (is_lub (set.Iio c) c),
  { have : c ∈ upper_bounds (set.Iio c) := λ y hy, le_of_lt hy,
    obtain ⟨b, b_up, bc⟩ : ∃ (b : β), b ∈ upper_bounds (set.Iio c) ∧ b < c,
      by simpa [is_lub, is_least, this, lower_bounds] using H,
    exact measure_mono_null (λ x hx, b_up hx) (hc b bc) },
  push_neg at H h,
  obtain ⟨u, u_mono, u_lt, u_lim, -⟩ : ∃ (u : ℕ → β), strict_mono u ∧ (∀ (n : ℕ), u n < c)
      ∧ tendsto u at_top (nhds c) ∧ ∀ (n : ℕ), u n ∈ set.Iio c :=
    H.exists_seq_strict_mono_tendsto_of_not_mem (lt_irrefl c) h,
  have h_Union : {x | f x < c} = ⋃ (n : ℕ), {x | f x ≤ u n},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_set_of_eq],
    split; intro h,
    { obtain ⟨n, hn⟩ := ((tendsto_order.1 u_lim).1 _ h).exists, exact ⟨n, hn.le⟩ },
    { obtain ⟨n, hn⟩ := h, exact hn.trans_lt (u_lt _), }, },
  rw [h_Union, measure_Union_null_iff],
  assume n,
  exact hc _ (u_lt n),
end

section ennreal

open_locale topological_space

lemma ae_le_of_forall_set_lintegral_le_of_sigma_finite [sigma_finite μ]
  {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g)
  (h : ∀ s, measurable_set s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ) :
  f ≤ᵐ[μ] g :=
begin
  have A : ∀ (ε N : ℝ≥0) (p : ℕ), 0 < ε →
    μ ({x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanning_sets μ p) = 0,
  { assume ε N p εpos,
    let s := {x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanning_sets μ p,
    have s_meas : measurable_set s,
    { have A : measurable_set {x | g x + ε ≤ f x} := measurable_set_le (hg.add measurable_const) hf,
      have B : measurable_set {x | g x ≤ N} := measurable_set_le hg measurable_const,
      exact (A.inter B).inter (measurable_spanning_sets μ p) },
    have s_lt_top : μ s < ∞ :=
      (measure_mono (set.inter_subset_right _ _)).trans_lt (measure_spanning_sets_lt_top μ p),
    have A : ∫⁻ x in s, g x ∂μ + ε * μ s ≤ ∫⁻ x in s, g x ∂μ + 0 := calc
      ∫⁻ x in s, g x ∂μ + ε * μ s = ∫⁻ x in s, g x ∂μ + ∫⁻ x in s, ε ∂μ :
        by simp only [lintegral_const, set.univ_inter, measurable_set.univ, measure.restrict_apply]
      ... = ∫⁻ x in s, (g x + ε) ∂μ : (lintegral_add hg measurable_const).symm
      ... ≤ ∫⁻ x in s, f x ∂μ : set_lintegral_mono (hg.add measurable_const) hf (λ x hx, hx.1.1)
      ... ≤ ∫⁻ x in s, g x ∂μ + 0 : by { rw [add_zero], exact h s s_meas s_lt_top },
    have B : ∫⁻ x in s, g x ∂μ ≠ ∞,
    { apply ne_of_lt,
      calc ∫⁻ x in s, g x ∂μ ≤ ∫⁻ x in s, N ∂μ :
        set_lintegral_mono hg measurable_const (λ x hx, hx.1.2)
      ... = N * μ s :
        by simp only [lintegral_const, set.univ_inter, measurable_set.univ, measure.restrict_apply]
      ... < ∞ : by simp only [lt_top_iff_ne_top, s_lt_top.ne, and_false,
        ennreal.coe_ne_top, with_top.mul_eq_top_iff, ne.def, not_false_iff, false_and, or_self] },
    have : (ε : ℝ≥0∞) * μ s ≤ 0 := ennreal.le_of_add_le_add_left B A,
    simpa only [ennreal.coe_eq_zero, nonpos_iff_eq_zero, mul_eq_zero, εpos.ne', false_or] },
  obtain ⟨u, u_mono, u_pos, u_lim⟩ : ∃ (u : ℕ → ℝ≥0), strict_anti u ∧ (∀ n, 0 < u n) ∧
    tendsto u at_top (nhds 0) := exists_seq_strict_anti_tendsto (0 : ℝ≥0),
  let s := λ (n : ℕ), {x | g x + u n ≤ f x ∧ g x ≤ (n : ℝ≥0)} ∩ spanning_sets μ n,
  have μs : ∀ n, μ (s n) = 0 := λ n, A _ _ _ (u_pos n),
  have B : {x | f x ≤ g x}ᶜ ⊆ ⋃ n, s n,
  { assume x hx,
    simp at hx,
    have L1 : ∀ᶠ n in at_top, g x + u n ≤ f x,
    { have : tendsto (λ n, g x + u n) at_top (𝓝 (g x + (0 : ℝ≥0))) :=
        tendsto_const_nhds.add (ennreal.tendsto_coe.2 u_lim),
      simp at this,
      exact eventually_le_of_tendsto_lt hx this },
    have L2 : ∀ᶠ (n : ℕ) in (at_top : filter ℕ), g x ≤ (n : ℝ≥0),
    { have : tendsto (λ (n : ℕ), ((n : ℝ≥0) : ℝ≥0∞)) at_top (𝓝 ∞),
      { simp only [ennreal.coe_nat],
        exact ennreal.tendsto_nat_nhds_top },
      exact eventually_ge_of_tendsto_gt (hx.trans_le le_top) this },
    apply set.mem_Union.2,
    exact ((L1.and L2).and (eventually_mem_spanning_sets μ x)).exists },
  refine le_antisymm _ bot_le,
  calc μ {x : α | (λ (x : α), f x ≤ g x) x}ᶜ ≤ μ (⋃ n, s n) : measure_mono B
  ... ≤ ∑' n, μ (s n) : measure_Union_le _
  ... = 0 : by simp only [μs, tsum_zero]
end

lemma ae_eq_of_forall_set_lintegral_eq_of_sigma_finite [sigma_finite μ]
  {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g)
  (h : ∀ s, measurable_set s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_set_lintegral_le_of_sigma_finite hf hg (λ s hs h's, le_of_eq (h s hs h's)),
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_set_lintegral_le_of_sigma_finite hg hf (λ s hs h's, ge_of_eq (h s hs h's)),
  filter_upwards [A, B],
  exact λ x, le_antisymm
end

end ennreal

section real

section real_finite_measure

variables [is_finite_measure μ] {f : α → ℝ}

/-- Don't use this lemma. Use `ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure`. -/
lemma ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable (hfm : measurable f)
  (hf : integrable f μ) (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have h_int_gt : ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top μ s))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall (λ x hxs, hxs), },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp (h_int_gt.trans_lt _),
  refine (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le _,
  swap, { simp_rw measure.restrict_restrict hs, exact hf_zero s hs, },
  refine (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _),
  cases (ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_eq_zero hμs_eq_top,
  { exact hμs_eq_zero, },
  { exact absurd hμs_eq_top (measure_lt_top μ s).ne, },
end

lemma ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf.1 with ⟨f', hf'_meas, hf_ae⟩,
  have hf'_integrable : integrable f' μ, from integrable.congr hf hf_ae,
  have hf'_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable hf'_meas
    hf'_integrable hf'_zero).trans hf_ae.symm.le,
end

end real_finite_measure

lemma ae_nonneg_restrict_of_forall_set_integral_nonneg_inter {f : α → ℝ} {t : set α} (hμt : μ t ≠ ∞)
  (hf : integrable_on f t μ) (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in (s ∩ t), f x ∂μ) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  haveI : fact (μ t < ∞) := ⟨lt_top_iff_ne_top.mpr hμt⟩,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure hf (λ s hs, _),
  simp_rw measure.restrict_restrict hs,
  exact hf_zero s hs,
end

lemma ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ] {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  apply ae_of_forall_measure_lt_top_ae_restrict,
  assume t t_meas t_lt_top,
  apply ae_nonneg_restrict_of_forall_set_integral_nonneg_inter t_lt_top.ne
    (hf_int_finite t t_meas t_lt_top),
  assume s s_meas,
  exact hf_zero _ (s_meas.inter t_meas)
    (lt_of_le_of_lt (measure_mono (set.inter_subset_right _ _)) t_lt_top)
end

lemma ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf : ae_fin_strongly_measurable f μ)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  let t := hf.sigma_finite_set,
  suffices : 0 ≤ᵐ[μ.restrict t] f,
    from ae_of_ae_restrict_of_ae_restrict_compl this hf.ae_eq_zero_compl.symm.le,
  haveI : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (λ s hs hμts, _)
    (λ s hs hμts, _),
  { rw [integrable_on, measure.restrict_restrict hs],
    rw measure.restrict_apply hs at hμts,
    exact hf_int_finite (s ∩ t) (hs.inter hf.measurable_set) hμts, },
  { rw measure.restrict_restrict hs,
    rw measure.restrict_apply hs at hμts,
    exact hf_zero (s ∩ t) (hs.inter hf.measurable_set) hμts, },
end

lemma integrable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg hf.ae_fin_strongly_measurable
  (λ s hs hμs, hf.integrable_on) hf_zero

lemma ae_nonneg_restrict_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμt
    (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) (λ s hs, _),
  refine (hf_zero (s ∩ t) (hs.inter ht) _),
  exact (measure_mono (set.inter_subset_right s t)).trans_lt (lt_top_iff_ne_top.mpr hμt),
end

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f,
    from h_and.1.mp (h_and.2.mono (λ x hx1 hx2, le_antisymm hx2 hx1)),
  refine ⟨_, ae_nonneg_restrict_of_forall_set_integral_nonneg hf_int_finite
    (λ s hs hμs, (hf_zero s hs hμs).symm.le) ht hμt⟩,
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f,
  { refine h_neg.mono (λ x hx, _),
    rw pi.neg_apply at hx,
    simpa using hx, },
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg
    (λ s hs hμs, (hf_int_finite s hs hμs).neg) (λ s hs hμs, _) ht hμt,
  simp_rw pi.neg_apply,
  rw [integral_neg, neg_nonneg],
  exact (hf_zero s hs hμs).le,
end

end real

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero {f : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  refine ae_eq_zero_of_forall_dual ℝ (λ c, _),
  refine ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real _ _ ht hμt,
  { assume s hs hμs,
    exact continuous_linear_map.integrable_comp c (hf_int_finite s hs hμs) },
  { assume s hs hμs,
    rw [continuous_linear_map.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs],
    exact continuous_linear_map.map_zero _ }
end

lemma ae_eq_restrict_of_forall_set_integral_eq {f g : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    exact sub_eq_zero.mpr (hfg_zero s hs hμs), },
  have hfg_int : ∀ s, measurable_set s → μ s < ∞ → integrable_on (f-g) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs),
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hfg_int hfg' ht hμt,
end

lemma ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_eq, ae_iff,
    measure.restrict_apply' (measurable_set.Union (measurable_spanning_sets μ))],
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from (measurable_spanning_sets μ n),
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne,
end

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f g : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)], },
  have hfg_int : ∀ s, measurable_set s → μ s < ∞ → integrable_on (f-g) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs),
  exact ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite hfg_int hfg,
end

lemma ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : ae_fin_strongly_measurable f μ) :
  f =ᵐ[μ] 0 :=
begin
  let t := hf.sigma_finite_set,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl this hf.ae_eq_zero_compl,
  haveI : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict,
  refine ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _,
  { intros s hs hμs,
    rw [integrable_on, measure.restrict_restrict hs],
    rw [measure.restrict_apply hs] at hμs,
    exact hf_int_finite _ (hs.inter hf.measurable_set) hμs, },
  { intros s hs hμs,
    rw [measure.restrict_restrict hs],
    rw [measure.restrict_apply hs] at hμs,
    exact hf_zero _ (hs.inter hf.measurable_set) hμs, },
end

lemma ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq {f g : α → E}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  f =ᵐ[μ] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)], },
  have hfg_int : ∀ s, measurable_set s → μ s < ∞ → integrable_on (f-g) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs),
  exact (hf.sub hg).ae_eq_zero_of_forall_set_integral_eq_zero hfg_int hfg,
end

lemma Lp.ae_eq_zero_of_forall_set_integral_eq_zero
  (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero hf_int_finite hf_zero
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma Lp.ae_eq_of_forall_set_integral_eq (f g : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim (hm : m ≤ m0)
  {f : α → E} (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : fin_strongly_measurable f (μ.trim hm)) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigma_finite,
  haveI : sigma_finite ((μ.restrict t).trim hm) := by rwa restrict_trim hm μ ht_meas at htμ,
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0,
  { rw [eventually_eq, ae_restrict_iff' (measurable_set.compl (hm _ ht_meas))],
    exact eventually_of_forall htf_zero, },
  have hf_meas_m : @measurable _ _ m _ f, from hf.measurable,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl this htf_zero,
  refine measure_eq_zero_of_trim_eq_zero hm _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _,
  { intros s hs hμs,
    rw [integrable_on, restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, measure.restrict_apply hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    refine integrable.trim hm _ hf_meas_m,
    exact hf_int_finite _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
  { intros s hs hμs,
    rw [restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, measure.restrict_apply hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    rw ← integral_trim hm hf_meas_m,
    exact hf_zero _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
end

lemma integrable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  have hf_Lp : mem_ℒp f 1 μ, from mem_ℒp_one_iff_integrable.mpr hf,
  let f_Lp := hf_Lp.to_Lp f,
  have hf_f_Lp : f =ᵐ[μ] f_Lp, from (mem_ℒp.coe_fn_to_Lp hf_Lp).symm,
  refine hf_f_Lp.trans _,
  refine Lp.ae_eq_zero_of_forall_set_integral_eq_zero f_Lp one_ne_zero ennreal.coe_ne_top _ _,
  { exact λ s hs hμs, integrable.integrable_on (L1.integrable_coe_fn _), },
  { intros s hs hμs,
    rw integral_congr_ae (ae_restrict_of_ae hf_f_Lp.symm),
    exact hf_zero s hs hμs, },
end

lemma integrable.ae_eq_of_forall_set_integral_eq (f g : α → E)
  (hf : integrable f μ) (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  exact integrable.ae_eq_zero_of_forall_set_integral_eq_zero (hf.sub hg) hfg',
end

end ae_eq_of_forall_set_integral_eq

section lintegral

lemma ae_measurable.ae_eq_of_forall_set_lintegral_eq {f g : α → ℝ≥0∞}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (hgi : ∫⁻ x, g x ∂μ ≠ ∞)
  (hfg : ∀ ⦃s⦄, measurable_set s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  refine ennreal.eventually_eq_of_to_real_eventually_eq
    (ae_lt_top' hf hfi).ne_of_lt (ae_lt_top' hg hgi).ne_of_lt
    (integrable.ae_eq_of_forall_set_integral_eq _ _
      (integrable_to_real_of_lintegral_ne_top hf hfi)
      (integrable_to_real_of_lintegral_ne_top hg hgi) (λ s hs hs', _)),
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { congr' 1,
    rw [lintegral_congr_ae (of_real_to_real_ae_eq _),
        lintegral_congr_ae (of_real_to_real_ae_eq _)],
    { exact hfg hs hs' },
    { refine (ae_lt_top' hg.restrict (ne_of_lt (lt_of_le_of_lt _ hgi.lt_top))),
      exact @set_lintegral_univ α _ μ g ▸ lintegral_mono_set (set.subset_univ _) },
    { refine (ae_lt_top' hf.restrict (ne_of_lt (lt_of_le_of_lt _ hfi.lt_top))),
      exact @set_lintegral_univ α _ μ f ▸ lintegral_mono_set (set.subset_univ _) } },
  -- putting the proofs where they are used is extremely slow
  exacts [ae_of_all _ (λ x, ennreal.to_real_nonneg), hg.ennreal_to_real.restrict,
          ae_of_all _ (λ x, ennreal.to_real_nonneg), hf.ennreal_to_real.restrict]
end

end lintegral

end measure_theory
