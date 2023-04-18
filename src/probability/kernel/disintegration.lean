/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.borel_space
import measure_theory.measure.stieltjes
import probability.kernel.invariance
import measure_theory.decomposition.radon_nikodym

/-!
# Disintegration of measures

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

-/

open measure_theory set filter

open_locale ennreal measure_theory topology

namespace probability_theory

variables {α β ι : Type*} {mα : measurable_space α}

lemma image_fst_prod (s : set α) (t : set β) (ht : t.nonempty) :
  prod.fst '' s ×ˢ t = s :=
begin
  ext1 x,
  simp only [mem_image, mem_prod, prod.exists, exists_and_distrib_right,
    exists_and_distrib_left, exists_eq_right, and_iff_left_iff_imp],
  exact λ _, ht,
end

lemma to_real_infi (f : α → ℝ≥0∞) (hf : ∀ a, f a ≠ ∞) :
  (⨅ i, f i).to_real = ⨅ i, (f i).to_real :=
begin
  casesI is_empty_or_nonempty α,
  { -- todo: real.cinfi_empty should be a simp lemma
    simp only [with_top.cinfi_empty, ennreal.top_to_real, real.cinfi_empty], },
  have h_ne_top : (⨅ i, f i) ≠ ∞,
  { refine ne_of_lt (lt_of_le_of_lt _ (hf h.some).lt_top),
    exact infi_le _ _, },
  refine le_antisymm _ _,
  { refine le_cinfi (λ a, (ennreal.to_real_le_to_real h_ne_top (hf a)).mpr _),
    exact infi_le _ _, },
  {
    sorry, },
end

lemma is_pi_system_Ioc_rat : @is_pi_system ℝ {S | ∃ (l u : ℚ) (h : l < u), Ioc (l : ℝ) u = S} :=
begin
  rintros s ⟨ls, us, hlus, rfl⟩ t ⟨lt, ut, hlut, rfl⟩ hst,
  rw [Ioc_inter_Ioc, sup_eq_max, inf_eq_min] at hst ⊢,
  refine ⟨max ls lt, min us ut, _, _⟩,
  { rw [nonempty_Ioc] at hst,
    exact_mod_cast hst, },
  { norm_cast, },
end

lemma is_pi_system_Iic_rat : @is_pi_system ℝ {S | ∃ (u : ℚ), Iic (u : ℝ) = S} :=
begin
  rintros s ⟨us, rfl⟩ t ⟨ut, rfl⟩ hst,
  rw [Iic_inter_Iic, inf_eq_min] at hst ⊢,
  refine ⟨min us ut, _⟩,
  norm_cast,
end

lemma borel_eq_generate_from_Ioc_rat :
  borel ℝ
    = measurable_space.generate_from {S : set ℝ | ∃ (l u : ℚ) (h : l < u), Ioc ↑l ↑u = S} :=
begin
  refine le_antisymm _ _,
  swap,
  { refine measurable_space.generate_from_le (λ t ht, _),
    obtain ⟨l, u, hlu, rfl⟩ := ht,
    exact measurable_set_Ioc, },
  rw real.borel_eq_generate_from_Ioo_rat,
  refine measurable_space.generate_from_le (λ t ht, _),
  simp_rw mem_Union at ht,
  obtain ⟨l, u, hlu, ht⟩ := ht,
  rw mem_singleton_iff at ht,
  have : t = ⋃ (r : Iio u), Ioc l r,
  { rw ht,
    ext1 x,
    simp only [mem_Ioo, coe_coe, Union_coe_set, mem_Iio, subtype.coe_mk, mem_Union, mem_Ioc,
      exists_prop],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨r, hxr, hru⟩ := exists_rat_btwn h.2,
      exact ⟨r, by exact_mod_cast hru, h.1, hxr.le⟩, },
    { obtain ⟨r, hru, hlx, hxr⟩ := h,
      refine ⟨hlx, hxr.trans_lt _⟩,
      exact_mod_cast hru, }, },
  rw this,
  refine measurable_set.Union (λ r, _),
  by_cases hlr : l < r,
  { exact measurable_space.measurable_set_generate_from ⟨l, r, hlr, rfl⟩, },
  { rw Ioc_eq_empty,
    { exact @measurable_set.empty _
      (measurable_space.generate_from {S : set ℝ | ∃ (l u : ℚ) (h : l < u), Ioc ↑l ↑u = S}), },
    { exact_mod_cast hlr, }, },
end

lemma borel_eq_generate_from_Iic_rat :
  borel ℝ
    = measurable_space.generate_from {S : set ℝ | ∃ (u : ℚ), Iic ↑u = S} :=
begin
  refine le_antisymm _ _,
  swap,
  { refine measurable_space.generate_from_le (λ t ht, _),
    obtain ⟨l, u, hlu, rfl⟩ := ht,
    exact measurable_set_Iic, },
  rw borel_eq_generate_from_Ioc_rat,
  refine measurable_space.generate_from_le (λ t ht, _),
  obtain ⟨l, u, hlu, rfl⟩ := ht,
  have : Ioc (l : ℝ) u = Iic u \ Iic l,
  { ext1 x,
    simp only [Iic_diff_Iic], },
  rw this,
  refine measurable_set.diff _ _,
  { exact measurable_space.measurable_set_generate_from ⟨u, rfl⟩, },
  { exact measurable_space.measurable_set_generate_from ⟨l, rfl⟩, },
end

include mα

noncomputable
def todo_r (ρ : measure (α × ℝ)) (r : ℚ) : measure α :=
measure.of_measurable (λ s hs, ρ (s ×ˢ (Iic r))) (by simp only [empty_prod, measure_empty])
  (λ f hf_meas hf_disj,
  begin
    rw [set.Union_prod_const, measure_Union],
    { intros i j hij,
      rw [function.on_fun, disjoint_prod],
      exact or.inl (hf_disj hij), },
    { exact λ i, measurable_set.prod (hf_meas i) measurable_set_Iic, }
  end)

lemma todo_r_apply (ρ : measure (α × ℝ)) (r : ℚ) {s : set α} (hs : measurable_set s) :
  todo_r ρ r s = ρ (s ×ˢ Iic r) :=
measure.of_measurable_apply s hs

lemma todo_r_mono (ρ : measure (α × ℝ)) {r r' : ℚ} (h_le : r ≤ r') :
  todo_r ρ r ≤ todo_r ρ r' :=
begin
  intros s hs,
  simp_rw todo_r_apply ρ _ hs,
  refine measure_mono (λ x hx, _),
  simp only [mem_preimage, mem_prod, mem_Iic] at hx ⊢,
  refine ⟨hx.1, hx.2.trans _⟩,
  exact_mod_cast h_le,
end

lemma todo_r_univ (ρ : measure (α × ℝ)) (r : ℚ) : todo_r ρ r univ = ρ (univ ×ˢ Iic r) :=
by rw [todo_r_apply ρ r measurable_set.univ]

noncomputable
def todo (ρ : measure (α × ℝ)) : measure α := ρ.map prod.fst

lemma todo_univ (ρ : measure (α × ℝ)) : todo ρ univ = ρ univ :=
by rw [todo, measure.map_apply measurable_fst measurable_set.univ, preimage_univ]

lemma todo_r_le_todo (ρ : measure (α × ℝ)) (r : ℚ) : todo_r ρ r ≤ todo ρ :=
begin
  intros s hs,
  simp_rw [todo, todo_r_apply ρ r hs, measure.map_apply measurable_fst hs],
  refine measure_mono (λ x hx, _),
  simp only [mem_preimage, mem_prod, mem_Iic] at hx ⊢,
  exact hx.1,
end

lemma todo_r_ac_todo (ρ : measure (α × ℝ)) (r : ℚ) : todo_r ρ r ≪ todo ρ :=
measure.absolutely_continuous_of_le (todo_r_le_todo ρ r)

instance {ρ : measure (α × ℝ)} [is_finite_measure ρ] : is_finite_measure (todo ρ) :=
by { rw todo, apply_instance, }

instance {ρ : measure (α × ℝ)} [is_finite_measure ρ] (r : ℚ) : is_finite_measure (todo_r ρ r) :=
is_finite_measure_of_le _ (todo_r_le_todo ρ _)

lemma infi_todo_r_gt (ρ : measure (α × ℝ)) (t : ℚ) {s : set α} (hs : measurable_set s)
  [is_finite_measure ρ] :
  (⨅ r : {r' : ℚ // t < r'}, todo_r ρ r s) = todo_r ρ t s :=
begin
  simp_rw [todo_r_apply ρ _ hs],
  rw ← measure_Inter_eq_infi,
  { congr,
    ext1 x,
    simp only [coe_coe, mem_Inter, mem_prod, mem_Iic, subtype.forall, subtype.coe_mk],
    refine ⟨λ h, _, λ h a hta, ⟨h.1, h.2.trans _⟩⟩,
    { refine ⟨(h (t+1) (lt_add_one _)).1, _⟩,
      refine le_of_forall_lt_rat_imp_le (λ q htq, (h q _).2),
      exact_mod_cast htq, },
    { exact_mod_cast hta.le, }, },
  { exact λ _, hs.prod measurable_set_Iic, },
  { refine (λ r r', ⟨min r r', λ x, _, λ x, _⟩);
      simp only [coe_coe, mem_prod, mem_Iic, and_imp];
      refine λ hxs hx_min, ⟨hxs, hx_min.trans _⟩,
    { exact_mod_cast (min_le_left r r'), },
    { exact_mod_cast (min_le_right r r'), }, },
  { exact ⟨⟨t+1, lt_add_one _⟩, measure_ne_top ρ _⟩, },
end

noncomputable
def rnd_r (ρ : measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ := measure.rn_deriv (todo_r ρ r) (todo ρ)

lemma with_density_rnd_r (ρ : measure (α × ℝ)) (r : ℚ) [is_finite_measure ρ] :
  (todo ρ).with_density (rnd_r ρ r) = todo_r ρ r :=
measure.absolutely_continuous_iff_with_density_rn_deriv_eq.mp (todo_r_ac_todo ρ r)

lemma set_lintegral_rnd_r_todo (ρ : measure (α × ℝ)) (r : ℚ) {s : set α} (hs : measurable_set s)
  [is_finite_measure ρ] :
  ∫⁻ x in s, rnd_r ρ r x ∂(todo ρ) = todo_r ρ r s :=
begin
  have : ∀ r, ∫⁻ x in s, rnd_r ρ r x ∂(todo ρ) = ∫⁻ x in s, (rnd_r ρ r * 1) x ∂(todo ρ),
  { simp only [mul_one, eq_self_iff_true, forall_const], },
  rw [this, ← set_lintegral_with_density_eq_set_lintegral_mul _ _ _ hs],
  { rw with_density_rnd_r ρ r,
    simp only [pi.one_apply, lintegral_one, measure.restrict_apply, measurable_set.univ,
      univ_inter], },
  { exact measure.measurable_rn_deriv _ _, },
  { rw (_ : (1 : α → ℝ≥0∞) = (λ _, 1)),
    { exact measurable_const, },
    { refl, }, },
end

lemma set_lintegral_infi_gt_rnd_r (ρ : measure (α × ℝ)) (t : ℚ) {s : set α} (hs : measurable_set s)
  [is_finite_measure ρ] :
  ∫⁻ x in s, ⨅ r : Ioi t, rnd_r ρ r x ∂(todo ρ) = todo_r ρ t s :=
calc ∫⁻ x in s, ⨅ r : Ioi t, rnd_r ρ r x ∂(todo ρ)
    = ⨅ r : Ioi t, ∫⁻ x in s, rnd_r ρ r x ∂(todo ρ) :
  begin
    sorry,
  end
... = ⨅ r : Ioi t, todo_r ρ r s :
  by { congr' with r : 1, exact set_lintegral_rnd_r_todo ρ r hs, }
... = todo_r ρ t s : infi_todo_r_gt ρ t hs

lemma rnd_r_mono (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), monotone (λ r, rnd_r ρ r a) :=
begin
  simp_rw [monotone, ae_all_iff],
  intros r r' hrr',
  refine ae_le_of_forall_set_lintegral_le_of_sigma_finite _ _ _,
  { exact measure.measurable_rn_deriv _ _, },
  { exact measure.measurable_rn_deriv _ _, },
  { intros s hs hs_fin,
    rw [set_lintegral_rnd_r_todo ρ r hs, set_lintegral_rnd_r_todo ρ r' hs],
    refine todo_r_mono ρ _ s hs,
    exact_mod_cast hrr', },
end

lemma rnd_r_le_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), ∀ r, rnd_r ρ r a ≤ 1 :=
begin
  rw ae_all_iff,
  intros r,
  refine ae_le_of_forall_set_lintegral_le_of_sigma_finite _ measurable_const _,
  { exact measure.measurable_rn_deriv _ _, },
  intros s hs hs_fin,
  rw set_lintegral_rnd_r_todo ρ r hs,
  simp only [pi.one_apply, lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
  exact todo_r_le_todo ρ r s hs,
end

lemma tendsto_todo_r_at_top (ρ : measure (α × ℝ))
  {s : set α} (hs : measurable_set s) :
  tendsto (λ r, todo_r ρ r s) at_top (𝓝 (todo ρ s)) :=
begin
  simp_rw [todo_r, todo, measure.of_measurable_apply _ hs,
    measure.map_apply measurable_fst hs, ← prod_univ],
  have : s ×ˢ univ = ⋃ r : ℚ, (s ×ˢ Iic (r : ℝ)),
  { ext1 x,
    simp only [mem_prod, mem_univ, and_true, mem_Union, mem_Iic, exists_and_distrib_left,
      iff_self_and],
    refine λ _, _,
    obtain ⟨r, hr⟩ := exists_rat_gt x.snd,
    exact ⟨r, hr.le⟩, },
  rw this,
  refine tendsto_measure_Union (λ r q hr_le_q x, _),
  simp only [mem_prod, mem_Iic, and_imp],
  refine λ hxs hxr, ⟨hxs, hxr.trans _⟩,
  exact_mod_cast hr_le_q,
end

lemma tendsto_todo_r_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  tendsto (λ r, todo_r ρ r s) at_bot (𝓝 0) :=
begin
  simp_rw [todo_r, measure.of_measurable_apply _ hs],
  have h_empty : ρ (s ×ˢ ∅) = 0,
  { simp only [prod_empty, measure_empty], },
  rw ← h_empty,
  have : s ×ˢ ∅ = ⋂ r : ℚ, (s ×ˢ Iic (r : ℝ)),
  { ext1 x,
    simp only [prod_empty, mem_empty_iff_false, mem_Inter, mem_prod, mem_Iic, false_iff, not_forall,
      not_and, not_le],
    obtain ⟨r, hr⟩ := exists_rat_lt x.snd,
    exact ⟨r, λ _, hr⟩, },
  rw this,
  suffices h_neg : tendsto (λ r : ℚ, ρ (s ×ˢ Iic (↑-r))) at_top (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic (↑-r)))),
  { have h_inter_eq : (⋂ r : ℚ, s ×ˢ Iic (↑-r)) = (⋂ r : ℚ, s ×ˢ Iic (r : ℝ)),
    { ext1 x,
      simp only [rat.cast_eq_id, id.def, mem_Inter, mem_prod, mem_Iic],
      refine ⟨λ h i, ⟨(h i).1, _⟩, λ h i, ⟨(h i).1, _⟩⟩; have h' := h (-i),
      { rw neg_neg at h', exact h'.2, },
      { exact h'.2, }, },
    rw h_inter_eq at h_neg,
    have h_fun_eq : (λ (r : ℚ), ρ (s ×ˢ Iic (r : ℝ))) = (λ (r : ℚ), ρ (s ×ˢ Iic ↑(- -r))),
    { simp_rw neg_neg, },
    rw h_fun_eq,
    exact h_neg.comp tendsto_neg_at_bot_at_top, },
  refine tendsto_measure_Inter (λ q, hs.prod measurable_set_Iic) _ ⟨0, measure_ne_top ρ _⟩,
  intros q r hqr x,
  simp only [mem_prod, mem_Iic, and_imp, rat.cast_neg],
  refine λ hxs hxr, ⟨hxs, hxr.trans (neg_le_neg _)⟩,
  exact_mod_cast hqr,
end

lemma tendsto_lintegral_rnd_r_at_top (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, rnd_r ρ r a ∂(todo ρ)) at_top (𝓝 (ρ univ)) :=
begin
  suffices : tendsto (λ r, todo_r ρ r univ) at_top (𝓝 (todo ρ univ)),
  { convert this,
    { ext1 r,
      rw [← set_lintegral_univ, set_lintegral_rnd_r_todo ρ _ measurable_set.univ], },
    { exact (todo_univ ρ).symm }, },
  exact tendsto_todo_r_at_top ρ measurable_set.univ,
end

lemma tendsto_lintegral_rnd_r_at_top' (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, rnd_r ρ r a ∂(todo ρ)) at_top (𝓝 (∫⁻ a, 1 ∂(todo ρ))) :=
begin
  convert tendsto_lintegral_rnd_r_at_top ρ,
  rw [lintegral_one, todo_univ],
end

lemma tendsto_lintegral_rnd_r_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, rnd_r ρ r a ∂(todo ρ)) at_bot (𝓝 0) :=
begin
  suffices : tendsto (λ r, todo_r ρ r univ) at_bot (𝓝 0),
  { convert this,
    ext1 r,
    rw [← set_lintegral_univ, set_lintegral_rnd_r_todo ρ _ measurable_set.univ], },
  exact tendsto_todo_r_at_bot ρ measurable_set.univ,
end

lemma lintegral_sub' {μ : measure α} {f g : α → ℝ≥0∞} (hg : ae_measurable g μ)
  (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
begin
  refine ennreal.eq_sub_of_add_eq hg_fin _,
  rw [← lintegral_add_right' _ hg],
  exact lintegral_congr_ae (h_le.mono $ λ x hx, tsub_add_cancel_of_le hx)
end

lemma tendsto_rnd_r_at_top_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), tendsto (λ r, rnd_r ρ r a) at_top (𝓝 1) :=
begin
  have h_mono := rnd_r_mono ρ,
  have h_le_one := rnd_r_le_one ρ,
  have h_exists : ∀ᵐ a ∂(todo ρ), ∃ l ≤ (1 : ℝ≥0∞), tendsto (λ r, rnd_r ρ r a) at_top (𝓝 l),
  { filter_upwards [h_mono, h_le_one] with a ha_mono ha_le_one,
    -- todo: no direct way to get the or.inr of this?
    have h_tendsto : tendsto (λ r, rnd_r ρ r a) at_top at_top
      ∨ ∃ l, tendsto (λ r, rnd_r ρ r a) at_top (𝓝 l) := tendsto_of_monotone ha_mono,
    cases h_tendsto with h_absurd h_tendsto,
    { rw monotone.tendsto_at_top_at_top_iff ha_mono at h_absurd,
      obtain ⟨r, hr⟩ := h_absurd 2,
      exact absurd (hr.trans (ha_le_one r)) ennreal.one_lt_two.not_le, },
    obtain ⟨l, hl⟩ := h_tendsto,
    exact ⟨l, le_of_tendsto' hl ha_le_one, hl⟩, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l ≤ (1 : ℝ≥0∞), tendsto (λ r, rnd_r ρ r a) at_top (𝓝 l) then h.some else 0,
  have h_tendsto_ℚ : ∀ᵐ a ∂(todo ρ), tendsto (λ r, rnd_r ρ r a) at_top (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec.some_spec },
  have h_tendsto_ℕ : ∀ᵐ a ∂(todo ρ), tendsto (λ n : ℕ, rnd_r ρ n a) at_top (𝓝 (F a)),
  { filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_coe_nat_at_top_at_top, },
  have hF_ae_meas : ae_measurable F (todo ρ),
  { refine ae_measurable_of_tendsto_metrizable_ae' (λ n, _) h_tendsto_ℕ,
    exact (measure.measurable_rn_deriv _ _).ae_measurable, },
  have hF_le_one : ∀ᵐ a ∂(todo ρ), F a ≤ 1,
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec.some, },
  suffices : ∀ᵐ a ∂(todo ρ), F a = 1,
  { filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  have h_lintegral_eq : ∫⁻ a, F a ∂(todo ρ) = ∫⁻ a, 1 ∂(todo ρ),
  { have h_lintegral : tendsto (λ r : ℕ, ∫⁻ a, rnd_r ρ r a ∂(todo ρ)) at_top
      (𝓝 (∫⁻ a, F a ∂(todo ρ))),
    { refine lintegral_tendsto_of_tendsto_of_monotone
        (λ _, (measure.measurable_rn_deriv _ _).ae_measurable) _ h_tendsto_ℕ,
      filter_upwards [h_mono] with a ha,
      refine λ n m hnm, ha _,
      exact_mod_cast hnm, },
    have h_lintegral' : tendsto (λ r : ℕ, ∫⁻ a, rnd_r ρ r a ∂(todo ρ)) at_top
      (𝓝 (∫⁻ a, 1 ∂(todo ρ))),
    { exact (tendsto_lintegral_rnd_r_at_top' ρ).comp tendsto_coe_nat_at_top_at_top, },
    exact tendsto_nhds_unique h_lintegral h_lintegral', },
  have : ∫⁻ a, (1 - F a) ∂todo ρ = 0,
  { rw [lintegral_sub' hF_ae_meas _ hF_le_one, h_lintegral_eq, tsub_self],
    calc ∫⁻ a, F a ∂(todo ρ) = ∫⁻ a, 1 ∂(todo ρ) : h_lintegral_eq
    ... = todo ρ univ : lintegral_one
    ... = ρ univ : todo_univ ρ
    ... ≠ ⊤ : measure_ne_top ρ _, },
  rw lintegral_eq_zero_iff' at this,
  { filter_upwards [this, hF_le_one] with ha h_one_sub_eq_zero h_le_one,
    rw [pi.zero_apply, tsub_eq_zero_iff_le] at h_one_sub_eq_zero,
    exact le_antisymm h_le_one h_one_sub_eq_zero, },
  { exact ae_measurable_const.sub hF_ae_meas, },
end

lemma tendsto_rnd_r_at_bot_zero (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), tendsto (λ r, rnd_r ρ r a) at_bot (𝓝 0) :=
begin
  have h_mono := rnd_r_mono ρ,
  have h_exists : ∀ᵐ a ∂(todo ρ), ∃ l, tendsto (λ r, rnd_r ρ r a) at_bot (𝓝 l),
  { sorry, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l, tendsto (λ r, rnd_r ρ r a) at_bot (𝓝 l) then h.some else 0,
  have h_tendsto_ℚ : ∀ᵐ a ∂(todo ρ), tendsto (λ r, rnd_r ρ r a) at_bot (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec, },
  have h_tendsto_ℕ : ∀ᵐ a ∂(todo ρ), tendsto (λ n : ℕ, rnd_r ρ (-n) a) at_top (𝓝 (F a)),
  { filter_upwards [h_tendsto_ℚ] with a ha,
    exact (ha.comp tendsto_neg_at_top_at_bot).comp tendsto_coe_nat_at_top_at_top, },
  have hF_ae_meas : ae_measurable F (todo ρ),
  { refine ae_measurable_of_tendsto_metrizable_ae' (λ n, _) h_tendsto_ℕ,
    exact (measure.measurable_rn_deriv _ _).ae_measurable, },
  suffices : ∀ᵐ a ∂(todo ρ), F a = 0,
  { filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  have h_lintegral_eq : ∫⁻ a, F a ∂(todo ρ) = 0,
  { have h_lintegral : tendsto (λ r : ℕ, ∫⁻ a, rnd_r ρ (-r) a ∂(todo ρ)) at_top
      (𝓝 (∫⁻ a, F a ∂(todo ρ))),
    { refine tendsto_lintegral_of_dominated_convergence (λ _, 1) _ _ _ h_tendsto_ℕ,
      { exact λ _, measure.measurable_rn_deriv _ _, },
      { intros n,
        filter_upwards [rnd_r_le_one ρ] with a ha using ha _, },
      { rw lintegral_one,
        exact measure_ne_top _ _, }, },
    have h_lintegral' : tendsto (λ r : ℕ, ∫⁻ a, rnd_r ρ (-r) a ∂(todo ρ)) at_top
      (𝓝 0),
    { have h_lintegral_eq : (λ r : ℕ, ∫⁻ a, rnd_r ρ (-r) a ∂(todo ρ)) = λ r, ρ (univ ×ˢ Iic (-r)),
      { ext1 n,
        rw [← set_lintegral_univ, set_lintegral_rnd_r_todo ρ _ measurable_set.univ, todo_r_univ],
        norm_cast, },
      rw h_lintegral_eq,
      have h_zero_eq_measure_Inter : (0 : ℝ≥0∞) = ρ (⋂ r : ℕ, univ ×ˢ Iic (-r)),
      { suffices : (⋂ r : ℕ, univ ×ˢ Iic (-(r : ℝ))) = ∅, by rwa [this, measure_empty],
        ext1 x,
        simp only [mem_Inter, mem_prod, mem_univ, mem_Iic, true_and, mem_empty_iff_false, iff_false,
          not_forall, not_le],
        simp_rw neg_lt,
        exact exists_nat_gt _, },
      rw h_zero_eq_measure_Inter,
      refine tendsto_measure_Inter (λ n, measurable_set.univ.prod measurable_set_Iic)
        (λ i j hij x, _) ⟨0, measure_ne_top ρ _⟩,
      simp only [mem_prod, mem_univ, mem_Iic, true_and],
      refine λ hxj, hxj.trans (neg_le_neg _),
      exact_mod_cast hij, },
    exact tendsto_nhds_unique h_lintegral h_lintegral', },
  rwa [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq,
end

lemma rnd_r_ae_eq_inf_gt (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), ∀ t : ℚ, (⨅ r : Ioi t, rnd_r ρ r a) = rnd_r ρ t a :=
begin
  rw ae_all_iff,
  intros t,
  refine ae_eq_of_forall_set_lintegral_eq_of_sigma_finite _ _ _,
  { exact measurable_infi (λ i, measure.measurable_rn_deriv _ _), },
  { exact measure.measurable_rn_deriv _ _, },
  intros s hs hs_fin,
  rw [set_lintegral_infi_gt_rnd_r ρ t hs, set_lintegral_rnd_r_todo ρ t hs],
end

open_locale classical

def rnd_prop (ρ : measure (α × ℝ)) (a : α) : Prop :=
monotone (λ r, rnd_r ρ r a) ∧ (∀ r, rnd_r ρ r a ≤ 1)
  ∧ (tendsto (λ r, rnd_r ρ r a) at_top (𝓝 1)) ∧ (tendsto (λ r, rnd_r ρ r a) at_bot (𝓝 0))
  ∧ (∀ t : ℚ, (⨅ r : Ioi t, rnd_r ρ r a) = rnd_r ρ t a)

lemma rnd_prop_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), rnd_prop ρ a :=
begin
  simp_rw [rnd_prop, eventually_and],
  exact ⟨rnd_r_mono ρ, rnd_r_le_one ρ, tendsto_rnd_r_at_top_one ρ,
    tendsto_rnd_r_at_bot_zero ρ, rnd_r_ae_eq_inf_gt ρ⟩,
end

def rnd_prop_set (ρ : measure (α × ℝ)) : set α :=
(to_measurable (todo ρ) {b | ¬ rnd_prop ρ b})ᶜ

lemma measurable_set_rnd_prop_set (ρ : measure (α × ℝ)) : measurable_set (rnd_prop_set ρ) :=
(measurable_set_to_measurable _ _).compl

lemma rnd_prop_of_mem_rnd_prop_set {ρ : measure (α × ℝ)} {a : α} (h : a ∈ rnd_prop_set ρ) :
  rnd_prop ρ a :=
begin
  rw [rnd_prop_set, mem_compl_iff] at h,
  have h_ss := subset_to_measurable (todo ρ) {b | ¬ rnd_prop ρ b},
  by_contra ha,
  exact h (h_ss ha),
end

lemma rnd_prop_set_subset (ρ : measure (α × ℝ)) :
  rnd_prop_set ρ ⊆ {a | rnd_prop ρ a} :=
λ x, rnd_prop_of_mem_rnd_prop_set

lemma todo_compl_rnd_prop_set (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  todo ρ (rnd_prop_set ρ)ᶜ = 0 :=
begin
  rw [rnd_prop_set, compl_compl, measure_to_measurable],
  exact rnd_prop_ae ρ,
end

lemma mem_rnd_prop_set_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂(todo ρ), a ∈ rnd_prop_set ρ :=
todo_compl_rnd_prop_set ρ

noncomputable
def rnd' (ρ : measure (α × ℝ)) : α → ℚ → ℝ :=
λ a, if a ∈ rnd_prop_set ρ then (λ r, (rnd_r ρ r a).to_real) else (λ r, if r < 0 then 0 else 1)

lemma rnd'_of_not_rnd_prop (ρ : measure (α × ℝ)) (a : α) (h : a ∉ rnd_prop_set ρ) :
  rnd' ρ a = λ r, if r < 0 then 0 else 1 :=
by simp only [rnd', h, if_false]

lemma rnd'_of_rnd_prop (ρ : measure (α × ℝ)) (a : α) (h : a ∈ rnd_prop_set ρ) (r : ℚ) :
  rnd' ρ a r = (rnd_r ρ r a).to_real :=
by simp only [rnd', h, if_true]

lemma monotone_rnd' (ρ : measure (α × ℝ)) (a : α) :
  monotone (rnd' ρ a) :=
begin
  by_cases h : a ∈ rnd_prop_set ρ,
  { simp only [rnd', h, if_true, forall_const, and_self],
    intros r r' hrr',
    have h' := rnd_prop_of_mem_rnd_prop_set h,
    have h_ne_top : ∀ r, rnd_r ρ r a ≠ ∞ := λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne,
    rw ennreal.to_real_le_to_real (h_ne_top _) (h_ne_top _),
    exact h'.1 hrr', },
  { simp only [rnd', h, if_false],
    intros x y hxy,
    dsimp only,
    split_ifs,
    { refl, },
    { exact zero_le_one, },
    { exact absurd (hxy.trans_lt h_2) h_1, },
    { refl, }, },
end

lemma measurable_rnd' (ρ : measure (α × ℝ)) (q : ℚ) :
  measurable (λ a, rnd' ρ a q) :=
begin
  rw rnd',
  simp_rw ite_apply,
  refine measurable.ite (measurable_set_rnd_prop_set ρ) _ measurable_const,
  exact (measure.measurable_rn_deriv _ _).ennreal_to_real,
end

lemma zero_le_rnd' (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  0 ≤ rnd' ρ a r :=
begin
  by_cases h : a ∈ rnd_prop_set ρ,
  { simp only [rnd', h, if_true, forall_const, and_self],
    exact ennreal.to_real_nonneg, },
  { simp only [rnd', h, if_false],
    split_ifs,
    { refl, },
    { exact zero_le_one, }, },
end

lemma rnd'_le_one (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  rnd' ρ a r ≤ 1 :=
begin
  by_cases h : a ∈ rnd_prop_set ρ,
  { have h' := rnd_prop_of_mem_rnd_prop_set h,
    rw rnd'_of_rnd_prop _ _ h,
    refine ennreal.to_real_le_of_le_of_real zero_le_one _,
    rw ennreal.of_real_one,
    exact h'.2.1 r, },
  { rw rnd'_of_not_rnd_prop _ _ h,
    dsimp only,
    split_ifs,
    exacts [zero_le_one, le_rfl], },
end

lemma tendsto_rnd'_at_bot (ρ : measure (α × ℝ)) (a : α) :
  tendsto (rnd' ρ a) at_bot (𝓝 0) :=
begin
  by_cases h : a ∈ rnd_prop_set ρ,
  { simp only [rnd', h, if_true],
    rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff],
    { exact (rnd_prop_of_mem_rnd_prop_set h).2.2.2.1, },
    { have h' := rnd_prop_of_mem_rnd_prop_set h,
      exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.zero_ne_top, }, },
  { simp only [rnd', h, if_false],
    refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_bot],
    refine ⟨-1, λ q hq, _⟩,
    rw if_pos,
    refine hq.trans_lt _,
    linarith, },
end

lemma tendsto_rnd'_at_top (ρ : measure (α × ℝ)) (a : α) :
  tendsto (rnd' ρ a) at_top (𝓝 1) :=
begin
  by_cases h : a ∈ rnd_prop_set ρ,
  { simp only [rnd', h, if_true],
    rw [← ennreal.one_to_real, ennreal.tendsto_to_real_iff],
    { exact (rnd_prop_of_mem_rnd_prop_set h).2.2.1, },
    { have h' := rnd_prop_of_mem_rnd_prop_set h,
      exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.one_ne_top, }, },
  { simp only [rnd', h, if_false],
    refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_top],
    refine ⟨0, λ q hq, _⟩,
    rw if_neg,
    exact not_lt.mpr hq, },
end

lemma rnd'_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, rnd' ρ a r) =ᵐ[todo ρ] λ a, (rnd_r ρ r a).to_real :=
begin
  filter_upwards [mem_rnd_prop_set_ae ρ] with a ha,
  exact rnd'_of_rnd_prop ρ a ha r,
end

lemma of_real_rnd'_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, ennreal.of_real (rnd' ρ a r)) =ᵐ[todo ρ] rnd_r ρ r :=
begin
  filter_upwards [rnd'_ae_eq ρ r, rnd_r_le_one ρ] with a ha ha_le_one,
  rw [ha, ennreal.of_real_to_real],
  exact ((ha_le_one r).trans_lt ennreal.one_lt_top).ne,
end

lemma rnd'_eq_inf_gt (ρ : measure (α × ℝ)) (a : α) (t : ℚ) :
  (⨅ r : Ioi t, rnd' ρ a r) = rnd' ρ a t :=
begin
  by_cases ha : a ∈ rnd_prop_set ρ,
  { simp_rw rnd'_of_rnd_prop ρ a ha,
    have ha' := rnd_prop_of_mem_rnd_prop_set ha,
    rw ← to_real_infi,
    { suffices : (⨅ (i : ↥(Ioi t)), rnd_r ρ ↑i a) = rnd_r ρ t a, by rw this,
      rw ← ha'.2.2.2.2, },
    { exact λ r, ((ha'.2.1 r).trans_lt ennreal.one_lt_top).ne, }, },
  { simp_rw rnd'_of_not_rnd_prop ρ a ha,
    have h_bdd : bdd_below (range (λ (r : ↥(Ioi t)), ite ((r : ℚ) < 0) (0 : ℝ) 1)),
    { refine ⟨0, λ x hx, _⟩,
      obtain ⟨y, rfl⟩ := mem_range.mpr hx,
      dsimp only,
      split_ifs,
      exacts [le_rfl, zero_le_one], },
    split_ifs with h h,
    { refine le_antisymm _ (le_cinfi (λ x, _)),
      { obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0,
        { refine ⟨t/2, _, _⟩,
          { linarith, },
          { linarith, }, },
        refine (cinfi_le h_bdd ⟨q, htq⟩).trans _,
        rw if_pos,
        rwa subtype.coe_mk, },
      { split_ifs,
        exacts [le_rfl, zero_le_one], }, },
    { refine le_antisymm _ _,
      { refine (cinfi_le h_bdd ⟨t+1, lt_add_one t⟩).trans _,
        split_ifs,
        exacts [zero_le_one, le_rfl], },
      { refine le_cinfi (λ x, _),
        rw if_neg,
        rw not_lt at h ⊢,
        exact h.trans (mem_Ioi.mp x.prop).le, }, }, },
end

noncomputable
def rnd'' (ρ : measure (α × ℝ)) : α → ℝ → ℝ :=
λ a t, ⨅ r : {r' : ℚ // t < r'}, rnd' ρ a r

lemma rnd''_eq_rnd' (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  rnd'' ρ a r = rnd' ρ a r :=
begin
  rw [← rnd'_eq_inf_gt ρ a r, rnd''],
  dsimp only,
  refine equiv.infi_congr _ _,
  { exact
    { to_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      inv_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      left_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta],
      right_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta], }, },
  { intro t,
    simp only [subtype.val_eq_coe, equiv.coe_fn_mk, subtype.coe_mk], },
end

lemma monotone_rnd'' (ρ : measure (α × ℝ)) (a : α) : monotone (rnd'' ρ a) :=
begin
  intros x y hxy,
  rw [rnd''],
  dsimp only,
  haveI : nonempty {r' : ℚ // y < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt y, exact ⟨⟨r, hrx⟩⟩, },
  refine le_cinfi (λ r, _),
  have hxr : x < r := hxy.trans_lt r.prop,
  refine (cinfi_le _ _).trans_eq _,
  { exact ⟨r.1, hxr⟩, },
  { refine ⟨0, λ z, _⟩,
    rw mem_range,
    rintros ⟨u, rfl⟩,
    exact zero_le_rnd' ρ a _, },
  { refl, },
end

lemma zero_le_rnd'' (ρ : measure (α × ℝ)) (a : α) (r : ℝ) :
  0 ≤ rnd'' ρ a r :=
begin
  haveI : nonempty {r' : ℚ // r < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt r, exact ⟨⟨r, hrx⟩⟩, },
  exact le_cinfi (λ r', zero_le_rnd' ρ a _),
end

lemma tendsto_rnd''_Ioi (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  tendsto (rnd'' ρ a) (𝓝[Ioi x] x) (𝓝 (rnd'' ρ a x)) :=
begin
  have h := monotone.tendsto_nhds_within_Ioi (monotone_rnd'' ρ a) x,
  convert h,
  rw Inf_image',
  have h' : (⨅ r : Ioi x, rnd'' ρ a r) = ⨅ r : {r' : ℚ // x < r'}, rnd'' ρ a r,
  { refine le_antisymm _ _,
    { haveI : nonempty {r' : ℚ // x < ↑r'},
      { obtain ⟨r, hrx⟩ := exists_rat_gt x,
        exact ⟨⟨r, hrx⟩⟩, },
      refine le_cinfi (λ r, _),
      obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop,
      refine cinfi_set_le _ _,
      { refine ⟨0, λ z, _⟩,
        rw mem_image,
        rintros ⟨u, hux, rfl⟩,
        exact zero_le_rnd'' ρ a u, },
      { rw mem_Ioi,
        refine hxy.trans _,
        exact_mod_cast hyr, }, },
    { refine le_cinfi (λ q, _),
      have hq := q.prop,
      rw mem_Ioi at hq,
      obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq,
      refine (cinfi_le _ _).trans _,
      { exact ⟨y, hxy⟩, },
      { refine ⟨0, λ z, _⟩,
        rw mem_range,
        rintros ⟨u, rfl⟩,
        exact zero_le_rnd'' ρ a _, },
      { refine monotone_rnd'' ρ a (le_trans _ hyq.le),
        norm_cast, }, }, },
  have h'' : (⨅ r : {r' : ℚ // x < r'}, rnd'' ρ a r) = ⨅ r : {r' : ℚ // x < r'}, rnd' ρ a r,
  { congr' with r,
    exact rnd''_eq_rnd' ρ a r, },
  rw [h', h''],
  refl,
end

lemma continuous_within_at_rnd'' (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  continuous_within_at (rnd'' ρ a) (Ici x) x :=
by { rw ← continuous_within_at_Ioi_iff_Ici, exact tendsto_rnd''_Ioi ρ a x, }

noncomputable
def rnd_stieltjes (ρ : measure (α × ℝ)) (a : α) : stieltjes_function :=
{ to_fun := rnd'' ρ a,
  mono' := monotone_rnd'' ρ a,
  right_continuous' := continuous_within_at_rnd'' ρ a }

noncomputable
def rnd_measure (ρ : measure (α × ℝ)) (a : α) : measure ℝ :=
(rnd_stieltjes ρ a).measure

lemma rnd_measure_Ioc (ρ : measure (α × ℝ)) (a : α) (q q' : ℚ) :
  rnd_measure ρ a (Ioc q q') = ennreal.of_real (rnd' ρ a q' - rnd' ρ a q) :=
by { rw [rnd_measure, stieltjes_function.measure_Ioc, ← rnd''_eq_rnd', ← rnd''_eq_rnd'], refl, }

lemma rnd_measure_Iic (ρ : measure (α × ℝ)) (a : α) (q : ℚ) :
  rnd_measure ρ a (Iic q) = ennreal.of_real (rnd' ρ a q) :=
begin
  have h_tendsto_1 : tendsto (λ r : ℚ, rnd_measure ρ a (Ioc r q)) at_bot
    (𝓝 (rnd_measure ρ a (Iic q))),
  { have h_Iic_eq_Union : Iic (q : ℝ) = ⋃ r : ℚ, Ioc (↑-r) q,
    { ext1 x,
      simp only [mem_Iic, mem_Union, mem_Ioc, exists_and_distrib_right, iff_and_self],
      intro h,
      simp_rw [rat.cast_neg, neg_lt],
      exact exists_rat_gt _, },
    rw h_Iic_eq_Union,
    suffices h_neg_top : tendsto (λ (r : ℚ), rnd_measure ρ a (Ioc (↑-r) q)) at_top
      (𝓝 (rnd_measure ρ a (⋃ (r : ℚ), Ioc (↑-r) q))),
    { have : (λ (r : ℚ), rnd_measure ρ a (Ioc (↑r) q)) = (λ r, rnd_measure ρ a (Ioc (↑-(-r)) q)),
      { simp_rw neg_neg, },
      rw this,
      exact h_neg_top.comp tendsto_neg_at_bot_at_top, },
    refine tendsto_measure_Union _,
    intros r r' hrr' x,
    simp only [rat.cast_neg, mem_Ioc, and_imp],
    refine λ hrx hxq, ⟨(neg_le_neg _).trans_lt hrx, hxq⟩,
    exact_mod_cast hrr', },
  have h_tendsto_2 :tendsto (λ r : ℚ, rnd_measure ρ a (Ioc r q)) at_bot
    (𝓝 (ennreal.of_real (rnd' ρ a q))),
  { simp_rw rnd_measure_Ioc,
    refine ennreal.tendsto_of_real _,
    nth_rewrite 0 ← sub_zero (rnd' ρ a q),
    refine tendsto.const_sub _ _,
    exact tendsto_rnd'_at_bot ρ a, },
  exact tendsto_nhds_unique h_tendsto_1 h_tendsto_2,
end

lemma rnd_measure_univ (ρ : measure (α × ℝ)) (a : α) :
  rnd_measure ρ a univ = 1 :=
begin
  have h_tendsto1 :
    tendsto (λ q : ℚ, rnd_measure ρ a (Iic q)) at_top (𝓝 (rnd_measure ρ a univ)),
  { have : univ = ⋃ q : ℚ, Iic (q : ℝ),
    { ext1 x,
      simp only [mem_univ, mem_Union, mem_Iic, true_iff],
      obtain ⟨r, hr⟩ := exists_rat_gt x,
      exact ⟨r, hr.le⟩, },
    rw this,
    refine tendsto_measure_Union (λ r q hr_le_q x, _),
    simp only [mem_Iic],
    refine λ hxr, hxr.trans _,
    exact_mod_cast hr_le_q, },
  have h_tendsto2 :
    tendsto (λ q : ℚ, rnd_measure ρ a (Iic q)) at_top (𝓝 1),
  { simp_rw rnd_measure_Iic ρ a,
    rw ← ennreal.of_real_one,
    refine ennreal.tendsto_of_real _,
    exact tendsto_rnd'_at_top ρ a, },
  exact tendsto_nhds_unique h_tendsto1 h_tendsto2,
end

instance (ρ : measure (α × ℝ)) (a : α) : is_probability_measure (rnd_measure ρ a) :=
⟨rnd_measure_univ ρ a⟩

lemma measurable_rnd_measure (ρ : measure (α × ℝ)) :
  measurable (rnd_measure ρ) :=
begin
  rw measure.measurable_measure,
  refine λ s hs, measurable_space.induction_on_inter
    borel_eq_generate_from_Iic_rat is_pi_system_Iic_rat _ _ _ _ hs,
  { simp only [measure_empty, measurable_const], },
  { rintros S ⟨u, rfl⟩,
    simp_rw rnd_measure_Iic ρ _ u,
    exact (measurable_rnd' ρ u).ennreal_of_real, },
  { intros t ht ht_rnd,
    have : (λ a, rnd_measure ρ a tᶜ) = (λ a, rnd_measure ρ a univ) - (λ a, rnd_measure ρ a t),
    { ext1 a,
      rw [measure_compl ht (measure_ne_top (rnd_measure ρ a) _), pi.sub_apply], },
    simp_rw [this, rnd_measure_univ ρ],
    exact measurable.sub measurable_const ht_rnd, },
  { intros f hf_disj hf_meas hf_rnd,
    simp_rw measure_Union hf_disj hf_meas,
    exact measurable.ennreal_tsum hf_rnd, },
end

noncomputable
def rnd_kernel (ρ : measure (α × ℝ)) : kernel α ℝ :=
{ val := λ a, rnd_measure ρ a,
  property := measurable_rnd_measure ρ }

lemma rnd_kernel_apply (ρ : measure (α × ℝ)) (a : α) :
  rnd_kernel ρ a = rnd_measure ρ a := rfl

lemma rnd_kernel_Iic (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  rnd_kernel ρ a (Iic r) = ennreal.of_real (rnd' ρ a r) :=
by rw [rnd_kernel_apply, rnd_measure_Iic ρ]

instance (ρ : measure (α × ℝ)) : is_markov_kernel (rnd_kernel ρ) :=
⟨λ a, by { rw rnd_kernel, apply_instance, } ⟩

lemma set_lintegral_rnd_kernel_Iic_rat (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, rnd_kernel ρ a (Iic r) ∂(todo ρ) = ρ (s ×ˢ Iic r) :=
begin
  simp_rw [rnd_kernel_Iic ρ],
  have : ∀ᵐ a ∂(todo ρ), a ∈ s → ennreal.of_real (rnd' ρ a r) = rnd_r ρ r a,
  { filter_upwards [of_real_rnd'_ae_eq ρ r] with a ha using λ _, ha, },
  rw [set_lintegral_congr_fun hs this, set_lintegral_rnd_r_todo ρ r hs],
  exact todo_r_apply ρ r hs,
end

lemma set_lintegral_rnd_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, rnd_kernel ρ a univ ∂(todo ρ) = ρ (s ×ˢ univ) :=
begin
  have h_univ : univ = ⋃ n : ℕ, Iic (n : ℝ),
  { ext1 x,
    simp only [mem_univ, mem_Union, mem_Iic, true_iff],
    obtain ⟨r, hr⟩ := exists_nat_gt x,
    exact ⟨r, hr.le⟩, },
  have h_tendsto1 : tendsto (λ n : ℕ, ∫⁻ a in s, rnd_kernel ρ a (Iic n) ∂(todo ρ)) at_top
    (𝓝 (∫⁻ a in s, rnd_kernel ρ a univ ∂(todo ρ))),
  { rw h_univ,
    refine tendsto_lintegral_of_dominated_convergence (λ _, 1) _ _ _ _,
    { exact λ n, kernel.measurable_coe _ measurable_set_Iic, },
    { refine λ n, eventually_of_forall (λ a, _),
      dsimp only,
      have : (n : ℝ) = ↑(n : ℚ) := rfl,
      rw [this, rnd_kernel_Iic, ← ennreal.of_real_one],
      exact ennreal.of_real_le_of_real (rnd'_le_one ρ a _), },
    { simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter, ne.def],
      exact measure_ne_top _ _, },
    { refine eventually_of_forall (λ a, tendsto_measure_Union (λ n m hnm x, _)),
      simp only [mem_Iic],
      refine λ hxn, hxn.trans _,
      exact_mod_cast hnm, }, },
  have h_tendsto2 : tendsto (λ n : ℕ, ∫⁻ a in s, rnd_kernel ρ a (Iic n) ∂(todo ρ)) at_top
    (𝓝 (ρ (s ×ˢ univ))),
  { have : ∀ n : ℕ, (n : ℝ) = ↑(n : ℚ) := λ n, rfl,
    simp_rw [this, set_lintegral_rnd_kernel_Iic_rat _ _ hs],
    have h_Union : s ×ˢ univ = ⋃ n : ℕ, s ×ˢ Iic ((n : ℚ) : ℝ),
    { rw ← prod_Union,
      congr,
      rw h_univ,
      congr, },
    rw h_Union,
    refine tendsto_measure_Union (λ n m hnm x, _),
    simp only [rat.cast_coe_nat, mem_prod, mem_Iic, and_imp],
    refine λ hxs hxn, ⟨hxs, hxn.trans _⟩,
    exact_mod_cast hnm, },
  exact tendsto_nhds_unique h_tendsto1 h_tendsto2,
end

lemma lintegral_rnd_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∫⁻ a, rnd_kernel ρ a univ ∂(todo ρ) = ρ univ :=
by rw [← set_lintegral_univ, set_lintegral_rnd_kernel_univ ρ measurable_set.univ, univ_prod_univ]

lemma set_lintegral_rnd_kernel_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) {t : set ℝ} (ht : measurable_set t) :
  ∫⁻ a in s, rnd_kernel ρ a t ∂(todo ρ) = ρ (s ×ˢ t) :=
begin
  refine measurable_space.induction_on_inter borel_eq_generate_from_Iic_rat is_pi_system_Iic_rat
    _ _ _ _ ht,
  { simp only [measure_empty, lintegral_const, zero_mul, prod_empty], },
  { rintros t ⟨q, rfl⟩,
    exact set_lintegral_rnd_kernel_Iic_rat ρ q hs, },
  { intros t ht ht_lintegral,
    have h_ne_top : ∀ a, rnd_kernel ρ a t ≠ ∞ := λ a, measure_ne_top _ _,
    calc ∫⁻ a in s, rnd_kernel ρ a tᶜ ∂todo ρ
        = ∫⁻ a in s, (rnd_kernel ρ a univ) - rnd_kernel ρ a t ∂todo ρ :
      by { congr' with a, rw measure_compl ht (h_ne_top _), }
    ... = ∫⁻ a in s, (rnd_kernel ρ a univ) ∂todo ρ - ∫⁻ a in s, rnd_kernel ρ a t ∂todo ρ :
      begin
        rw lintegral_sub,
        { exact kernel.measurable_coe _ ht, },
        { rw ht_lintegral,
          exact measure_ne_top ρ _, },
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
      end
    ... = ρ (s ×ˢ univ) - ρ (s ×ˢ t) : by rw [set_lintegral_rnd_kernel_univ ρ hs, ht_lintegral]
    ... = ρ (s ×ˢ tᶜ) :
      begin
        rw ← measure_diff _ (hs.prod ht) (measure_ne_top ρ _),
        { rw [prod_diff_prod, compl_eq_univ_diff],
          simp only [diff_self, empty_prod, union_empty], },
        { rw prod_subset_prod_iff,
          exact or.inl ⟨subset_rfl, subset_univ t⟩, },
      end, },
  { intros f hf_disj hf_meas hf_eq,
    simp_rw measure_Union hf_disj hf_meas,
    rw [lintegral_tsum (λ i, (kernel.measurable_coe _ (hf_meas i)).ae_measurable.restrict),
      prod_Union, measure_Union],
    { congr' with i : 1,
      exact hf_eq i, },
    { intros i j hij,
      rw [function.on_fun, disjoint_prod],
      exact or.inr (hf_disj hij), },
    { exact λ i, measurable_set.prod hs (hf_meas i), }, },
end

lemma lintegral_rnd_kernel (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set (α × ℝ)} (hs : measurable_set s) :
  ∫⁻ a, rnd_kernel ρ a {x | (a, x) ∈ s} ∂(todo ρ) = ρ s :=
begin
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp only [mem_empty_iff_false, set_of_false, measure_empty, lintegral_const, zero_mul], },
  { intros t ht,
    rw mem_image2 at ht,
    obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := ht,
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂,
    { intros a ha,
      simp only [ha, prod_mk_mem_set_prod_eq, true_and, set_of_mem_eq], },
    cases eq_empty_or_nonempty t₂ with h h,
    { simp only [h, prod_empty, mem_empty_iff_false, set_of_false, measure_empty, lintegral_const,
        zero_mul], },
    have h_int_eq : ∫⁻ a, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂todo ρ
      = ∫⁻ a in t₁, rnd_kernel ρ a t₂ ∂todo ρ,
    { rw ← lintegral_add_compl _ ht₁,
      have h_eq1 : ∫⁻ a in t₁, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂todo ρ
        = ∫⁻ a in t₁, rnd_kernel ρ a t₂ ∂todo ρ,
      { refine set_lintegral_congr_fun ht₁ (eventually_of_forall (λ a ha, _)),
        rw h_prod_eq_snd a ha, },
      have h_eq2 : ∫⁻ a in t₁ᶜ, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂todo ρ = 0,
      { suffices h_eq_zero : ∀ a ∈ t₁ᶜ, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = 0,
        { rw set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero),
          simp only [lintegral_const, zero_mul], },
        intros a hat₁,
        suffices : {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = ∅, by rw [this, measure_empty],
        ext1 x,
        simp only [prod_mk_mem_set_prod_eq, mem_set_of_eq, mem_empty_iff_false, iff_false, not_and],
        exact λ ha, absurd ha hat₁, },
      rw [h_eq1, h_eq2, add_zero], },
    rw h_int_eq,
    exact set_lintegral_rnd_kernel_prod ρ ht₁ ht₂, },
  { intros t ht ht_eq,
    calc ∫⁻ a, rnd_kernel ρ a {x : ℝ | (a, x) ∈ tᶜ} ∂todo ρ
        = ∫⁻ a, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t}ᶜ ∂todo ρ : rfl
    ... = ∫⁻ a, rnd_kernel ρ a univ - rnd_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂todo ρ :
      begin
        congr' with a : 1,
        rw measure_compl _ (measure_ne_top (rnd_kernel ρ a) _),
        exact measurable_prod_mk_left ht,
      end
    ... = ∫⁻ a, rnd_kernel ρ a univ ∂todo ρ - ∫⁻ a, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂todo ρ :
      begin
        have h_le : (λ a, rnd_kernel ρ a {x : ℝ | (a, x) ∈ t}) ≤ᵐ[todo ρ] λ a, rnd_kernel ρ a univ,
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
        rw lintegral_sub _ _ h_le,
        { exact kernel.measurable_prod_mk_mem _ ht, },
        { refine ((lintegral_mono_ae h_le).trans_lt _).ne,
          rw lintegral_rnd_kernel_univ,
          exact measure_lt_top ρ univ, },
      end
    ... = ρ univ - ρ t : by rw [ht_eq, lintegral_rnd_kernel_univ]
    ... = ρ tᶜ : (measure_compl ht (measure_ne_top _ _)).symm, },
  { intros f hf_disj hf_meas hf_eq,
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f i} = ⋃ i, {x | (a, x) ∈ f i},
    { intros a,
      ext1 x,
      simp only [mem_Union, mem_set_of_eq], },
    simp_rw h_eq,
    have h_disj : ∀ a, pairwise (disjoint on (λ i, {x | (a, x) ∈ f i})),
    { intros a i j hij,
      have h_disj := hf_disj hij,
      rw [function.on_fun, disjoint_iff_inter_eq_empty] at h_disj ⊢,
      ext1 x,
      simp only [mem_inter_iff, mem_set_of_eq, mem_empty_iff_false, iff_false],
      intros h_mem_both,
      suffices : (a, x) ∈ ∅, by rwa mem_empty_iff_false at this,
      rwa [← h_disj, mem_inter_iff], },
    have h_meas : ∀ a i, measurable_set {x | (a, x) ∈ f i},
    { exact λ a i, measurable_prod_mk_left (hf_meas i), },
    calc ∫⁻ a, rnd_kernel ρ a (⋃ i, {x | (a, x) ∈ f i}) ∂(todo ρ)
        = ∫⁻ a, ∑' i, rnd_kernel ρ a {x | (a, x) ∈ f i} ∂(todo ρ) :
          by { congr' with a : 1, rw measure_Union (h_disj a) (h_meas a), }
    ... = ∑' i, ∫⁻ a, rnd_kernel ρ a {x | (a, x) ∈ f i} ∂(todo ρ) :
          begin
            rw lintegral_tsum (λ i : ℕ, measurable.ae_measurable _),
            exact kernel.measurable_prod_mk_mem _ (hf_meas i),
          end
    ... = ∑' i, ρ (f i) : by { congr' with i : 1, exact hf_eq i, }
    ... = ρ (Union f) : (measure_Union hf_disj hf_meas).symm, },
end

open_locale probability_theory

-- todo define someting to have a nicer expression?
theorem disintegration (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ρ = ((kernel.const unit (todo ρ)) ⊗ₖ (kernel.prod_mk_left (rnd_kernel ρ) unit)) (unit.star) :=
begin
  ext1 s hs,
  rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  rw lintegral_rnd_kernel ρ hs,
end

end probability_theory
