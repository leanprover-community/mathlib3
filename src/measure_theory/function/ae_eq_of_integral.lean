/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import analysis.normed_space.dual
import measure_theory.function.strongly_measurable

/-! # From equality of integrals to equality of functions -/


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

lemma ae_eq_zero_of_forall_dual [normed_group E] [normed_space 𝕜 E]
  [second_countable_topology (dual 𝕜 E)]
  {f : α → E} (hf : ∀ c : dual 𝕜 E, (λ x, ⟪f x, c⟫) =ᵐ[μ] 0) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq (dual 𝕜 E),
  have hs : dense_range s := dense_range_dense_seq _,
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, ⟪f x, s n⟫ = (0 : 𝕜), from λ n, hf (s n),
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪f x, s n⟫ = (0 : 𝕜), by rwa ae_all_iff,
  refine hf'.mono (λ x hx, eq_zero_of_forall_dual_eq_zero 𝕜 (λ c, _)),
  have h_closed : is_closed {c : dual 𝕜 E | ⟪f x, c⟫ = (0 : 𝕜)},
  { refine is_closed_eq _ continuous_const,
    have h_fun_eq : (λ (c : dual 𝕜 E), ⟪f x, c⟫) = inclusion_in_double_dual 𝕜 E (f x),
      by { ext1 c, rw ← dual_def 𝕜 E (f x) c, },
    rw h_fun_eq,
    continuity, },
  exact @is_closed_property ℕ (dual 𝕜 E) _ s (λ c, ⟪f x, c⟫ = (0 : 𝕜)) hs h_closed (λ n, hx n) c,
end

end ae_eq_of_forall


variables {𝕜 E' : Type*} [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  {m m0 : measurable_space α} {μ : measure α} {s t : set α}
  [inner_product_space 𝕜 E] [measurable_space E] [borel_space E] [second_countable_topology E]
  [inner_product_space 𝕜 E'] [measurable_space E'] [borel_space E'] [second_countable_topology E']
  [complete_space E'] [normed_space ℝ E']
  {p : ℝ≥0∞}

section ae_eq_of_forall_set_integral_eq

lemma ae_const_le_iff_forall_lt_measure_zero (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  have h_Union : {x | f x < c} = ⋃ (r : ℚ) (hr : ↑r < c), {x | f x ≤ r},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_set_of_eq],
    split; intro h,
    { obtain ⟨q, lt_q, q_lt⟩ := exists_rat_btwn h, exact ⟨q, q_lt, lt_q.le⟩, },
    { obtain ⟨q, q_lt, q_le⟩ := h, exact q_le.trans_lt q_lt, }, },
  rw [h_Union, measure_Union_null_iff],
  split; intros h b,
  { intro hbc,
    obtain ⟨r, hr⟩ := exists_rat_btwn hbc,
    specialize h r,
    simp only [hr.right, set.Union_pos] at h,
    refine measure_mono_null (λ x hx, _) h,
    rw set.mem_set_of_eq at hx ⊢,
    exact hx.trans hr.1.le, },
  { by_cases hbc : ↑b < c,
    { simp only [hbc, set.Union_pos],
      exact h _ hbc, },
    { simp [hbc], }, },
end

section real

section real_finite_measure

variables [finite_measure μ] {f : α → ℝ}

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

lemma ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ]
  {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_le, ae_iff,
    measure.restrict_apply'],
  swap,
  { exact measurable_set.Union (measurable_spanning_sets μ), },
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from (measurable_spanning_sets μ n),
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμn.ne
    (hf_int_finite (S n) h_meas_n hμn) (λ s hs, _),
  exact hf_zero (s ∩ S n) (hs.inter h_meas_n)
    ((measure_mono (set.inter_subset_right _ _)).trans_lt hμn),
end

lemma integrable.ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ]
  {f : α → ℝ}
  (hf : integrable f μ) (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (λ s hs hμs, hf.integrable_on) hf_zero

lemma ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf : ae_fin_strongly_measurable f μ)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  let t := hf.sigma_finite_set,
  suffices : 0 ≤ᵐ[μ.restrict t] f,
    from ae_of_ae_restrict_of_ae_restrict_compl hf.measurable_set this hf.ae_eq_zero_compl.symm.le,
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

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ {f : α → ℝ}
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

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero_𝕜 {f : α → 𝕜}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  suffices h_re_im : (∀ᵐ x ∂(μ.restrict t), is_R_or_C.re (f x) = 0)
    ∧ ∀ᵐ x ∂(μ.restrict t), is_R_or_C.im (f x) = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rwa [is_R_or_C.ext_iff, pi.zero_apply, add_monoid_hom.map_zero, add_monoid_hom.map_zero], },
  have hf_re : ∀ s, measurable_set s → μ s < ∞ → integrable_on (λ x, is_R_or_C.re (f x)) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).re,
  have hf_im : ∀ s, measurable_set s → μ s < ∞ → integrable_on (λ x, is_R_or_C.im (f x)) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).im,
  have hf_zero_re : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.re (f x) ∂μ = 0,
  { intros s hs hμs,
    rw [integral_re (hf_int_finite s hs hμs), hf_zero s hs hμs, is_R_or_C.zero_re'], },
  have hf_zero_im : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.im (f x) ∂μ = 0,
  { intros s hs hμs,
    rw [integral_im (hf_int_finite s hs hμs), hf_zero s hs hμs],
    simp only [add_monoid_hom.map_zero], },
  exact ⟨ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_re hf_zero_re ht hμt,
    ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_im hf_zero_im ht hμt⟩,
end

lemma sigma_finite_restrict_union {α} {m : measurable_space α} {μ : measure α} {s t : set α}
  (hs : sigma_finite (μ.restrict s)) (ht : sigma_finite (μ.restrict t)) :
  sigma_finite (μ.restrict (s ∪ t)) :=
begin
  let S := spanning_sets (μ.restrict s),
  have hS_meas := λ n, measurable_spanning_sets (μ.restrict s) n,
  let T := spanning_sets (μ.restrict t),
  have hT_meas := λ n, measurable_spanning_sets (μ.restrict t) n,
  use (λ n, S n ∩ T n),
  { exact λ n, (hS_meas n).inter (hT_meas n), },
  { intros n,
    rw [measure.restrict_apply ((hS_meas n).inter (hT_meas n)), set.inter_union_distrib_left],
    refine (measure_union_le _ _).trans_lt (ennreal.add_lt_top.mpr ⟨_, _⟩),
    { have h_subset : S n ∩ T n ∩ s ⊆ S n ∩ s,
      { rw [set.inter_assoc, set.inter_comm, set.inter_assoc, set.inter_comm s],
        exact set.inter_subset_right _ _, },
      refine (measure_mono h_subset).trans_lt _,
      have h := measure_spanning_sets_lt_top (μ.restrict s) n,
      rwa measure.restrict_apply (hS_meas n) at h, },
    { have h_subset : S n ∩ T n ∩ t ⊆ T n ∩ t,
      { rw set.inter_assoc,
        exact set.inter_subset_right _ _, },
      refine (measure_mono h_subset).trans_lt _,
      have h := measure_spanning_sets_lt_top (μ.restrict t) n,
      rwa measure.restrict_apply (hT_meas n) at h, }, },
  { rw [set.Union_inter_of_monotone (monotone_spanning_sets (μ.restrict s))
      (monotone_spanning_sets (μ.restrict t)), Union_spanning_sets (μ.restrict s),
      Union_spanning_sets (μ.restrict t), set.univ_inter], },
end

lemma fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
  [topological_space β] [t2_space β] [has_zero β] {m : measurable_space α} {μ : measure α} :
  fin_strongly_measurable f μ ↔ (strongly_measurable f
    ∧ (∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t))) :=
⟨λ hf, ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩,
  λ hf, hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1
    hf.2.some_spec.2.2⟩

lemma strongly_measurable.add {α β} [measurable_space α] [topological_space β] [has_add β]
  [has_continuous_add β] {f g : α → β}
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f + g) :=
⟨λ n, hf.approx n + hg.approx n, λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

lemma strongly_measurable.neg {α β} [measurable_space α] [topological_space β] [add_group β]
  [topological_add_group β] {f : α → β} (hf : strongly_measurable f) :
  strongly_measurable (-f) :=
⟨λ n, - hf.approx n, λ x, (hf.tendsto_approx x).neg⟩

lemma strongly_measurable.sub {α β} [measurable_space α] [topological_space β] [has_sub β]
  [has_continuous_sub β] {f g : α → β}
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f - g) :=
⟨λ n, hf.approx n - hg.approx n, λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

lemma fin_strongly_measurable.add {α β} [topological_space β] [add_monoid β] [has_continuous_add β]
  {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f + g) μ :=
⟨λ n, hf.approx n + hg.approx n,
  λ n, (measure_mono (function.support_add _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

lemma fin_strongly_measurable.neg {α β} [topological_space β] [add_group β]
  [topological_add_group β] {m : measurable_space α} {μ : measure α} {f : α → β}
  (hf : fin_strongly_measurable f μ) :
  fin_strongly_measurable (-f) μ :=
begin
  refine ⟨λ n, -hf.approx n, λ n, _, λ x, (hf.tendsto_approx x).neg⟩,
  push_cast,
  suffices : μ (function.support (λ x, - (hf.approx n) x)) < ∞,
    by convert this,
  rw function.support_neg (hf.approx n),
  exact hf.fin_support_approx n,
end

lemma fin_strongly_measurable.sub {α β} [topological_space β] [add_group β] [has_continuous_sub β]
  {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f - g) μ :=
⟨λ n, hf.approx n - hg.approx n,
  λ n, (measure_mono (function.support_sub _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

lemma ae_fin_strongly_measurable.add {α β} [topological_space β] [add_monoid β]
  [has_continuous_add β] {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f + g) μ :=
⟨hf.some + hg.some, hf.some_spec.1.add hg.some_spec.1, hf.some_spec.2.add hg.some_spec.2⟩

lemma ae_fin_strongly_measurable.neg {α β} [topological_space β] [add_group β]
  [topological_add_group β] {m : measurable_space α} {μ : measure α} {f : α → β}
  (hf : ae_fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable (-f) μ :=
⟨-hf.some, hf.some_spec.1.neg, hf.some_spec.2.neg⟩

lemma ae_fin_strongly_measurable.sub {α β} [topological_space β] [add_group β]
  [has_continuous_sub β] {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f - g) μ :=
⟨hf.some - hg.some, hf.some_spec.1.sub hg.some_spec.1, hf.some_spec.2.sub hg.some_spec.2⟩

variables [is_scalar_tower ℝ 𝕜 E']
include 𝕜

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero {f : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  refine ae_eq_zero_of_forall_inner (λ c, _),
  refine ae_eq_zero_restrict_of_forall_set_integral_eq_zero_𝕜 _ _ ht hμt,
  { exact λ s hs hμs, (hf_int_finite s hs hμs).const_inner c, },
  { intros s hs hμs,
    rw integral_inner (hf_int_finite s hs hμs) c,
    simp [hf_zero s hs hμs], },
end

lemma ae_eq_restrict_of_forall_set_integral_eq {f g : α → E'}
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

lemma ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f : α → E'}
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

lemma ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : ae_fin_strongly_measurable f μ) :
  f =ᵐ[μ] 0 :=
begin
  let t := hf.sigma_finite_set,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl hf.measurable_set this hf.ae_eq_zero_compl,
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

lemma ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq {f g : α → E'}
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
  (f : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero hf_int_finite hf_zero
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma Lp.ae_eq_of_forall_set_integral_eq (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim (hm : m ≤ m0)
  {f : α → E'} (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : fin_strongly_measurable f (μ.trim hm)) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigma_finite,
  haveI : @sigma_finite _ m ((μ.restrict t).trim hm) := by rwa restrict_trim hm μ ht_meas at htμ,
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0,
  { rw [eventually_eq, ae_restrict_iff' (measurable_set.compl (hm _ ht_meas))],
    exact eventually_of_forall htf_zero, },
  have hf_meas_m : measurable[m] f, from hf.measurable,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl (hm t ht_meas) this htf_zero,
  refine measure_eq_zero_of_trim_eq_zero hm _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _,
  { intros s hs hμs,
    rw [integrable_on, restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, @measure.restrict_apply _ m _ _ _ hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    refine integrable.trim hm _ hf_meas_m,
    exact hf_int_finite _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
  { intros s hs hμs,
    rw [restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, @measure.restrict_apply _ m _ _ _ hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    rw ← integral_trim hm hf_meas_m,
    exact hf_zero _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
end

lemma Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero
  (hm : m ≤ m0) (f : Lp_meas E' 𝕜 m p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top,
  refine hfg.trans _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

lemma Lp.ae_eq_zero_of_forall_set_integral_eq_zero'
  (hm : m ≤ m0) (f : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf_meas : ae_measurable' m f μ) :
  f =ᵐ[μ] 0 :=
begin
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩,
  have hf_f_meas : f =ᵐ[μ] f_meas, by simp only [coe_fn_coe_base, subtype.coe_mk],
  refine hf_f_meas.trans _,
  refine Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

/-- **Unicity of the conditional expectation**. -/
lemma Lp.ae_eq_of_forall_set_integral_eq'
  (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hf_meas : ae_measurable' m f μ) (hg_meas : ae_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : ⇑(f-g) =ᵐ[μ] 0,
    by { rw ← sub_ae_eq_zero, exact (Lp.coe_fn_sub f g).symm.trans h_sub, },
  have hfg' : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g)),
    rw integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on ⇑(f-g) s μ,
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))],
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs), },
  have hfg_meas : ae_measurable' m ⇑(f - g) μ,
    from ae_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm,
  exact Lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm (f-g) hp_ne_zero hp_ne_top hfg_int hfg'
    hfg_meas,
end

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f g : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_eq, ae_iff,
    measure.restrict_apply'],
  swap,
  { refine measurable_set.Union _ ,
    exact measurable_spanning_sets μ, },
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from measurable_spanning_sets μ n,
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  exact ae_eq_restrict_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg_zero h_meas_n
    hμn.ne,
end

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)]
  {f g : α → E'}
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  rw ← ae_eq_trim_iff_of_ae_measurable' hm hfm hgm,
  have hf_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ _ (hfm.mk f) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hfm.measurable_mk,
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk), },
  have hg_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ _ (hgm.mk g) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hgm.measurable_mk,
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk), },
  have hfg_mk_eq : ∀ s : set α, measurable_set[m] s → μ.trim hm s < ∞ →
    @integral _ _ m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) (hfm.mk f)
      = @integral _ _ m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) (hgm.mk g),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.measurable_mk,
      ← integral_trim hm hgm.measurable_mk, integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)],
    exact hfg_eq s hs hμs, },
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq,
end

lemma integrable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E'} (hf : integrable f μ)
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

lemma integrable.ae_eq_of_forall_set_integral_eq (f g : α → E')
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

omit 𝕜
end ae_eq_of_forall_set_integral_eq

end measure_theory
