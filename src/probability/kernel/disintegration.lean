/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.borel_space
import measure_theory.measure.stieltjes
import probability.kernel.composition
import measure_theory.decomposition.radon_nikodym

/-!
# Disintegration of measures

We prove that for any finite measure `ρ` on `α × ℝ`, there exists a kernel
`cond_kernel ρ : kernel α ℝ` and a measure `ρ.fst : measure α` such that
`ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) (unit.star)`.
Equivalently, for any measurable space `γ`,
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ)`.

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Future extensions

* We can obtain a disintegration for measures on `α × E` for a standard borel space `E` by using
  that `E` is measurably equivalent to `ℝ`, `ℤ` or a finite set.
* The finite measure hypothesis can be weakened to σ-finite. The proof uses the finite case.
* Using the Radon-Nikodym theorem for kernels, we can extend this to disintegration of
  kernels.
* The conditional cdf construction in this file can give the cdf of a real measure by using the
  conditional cdf of a measure on `unit × ℝ`.

-/

open measure_theory set filter

open_locale nnreal ennreal measure_theory topology probability_theory

section aux_lemmas_to_be_moved

variables {α β ι : Type*}

lemma prod_Inter {s : set α} {t : ι → set β} [hι : nonempty ι] :
  s ×ˢ (⋂ i, t i) = ⋂ i, s ×ˢ (t i) :=
begin
  ext x,
  simp only [mem_prod, mem_Inter],
  exact ⟨λ h i, ⟨h.1, h.2 i⟩, λ h, ⟨(h hι.some).1, λ i, (h i).2⟩⟩,
end

lemma real.Union_Iic_rat : (⋃ r : ℚ, Iic (r : ℝ)) = univ :=
begin
  ext1,
  simp only [mem_Union, mem_Iic, mem_univ, iff_true],
  obtain ⟨r, hr⟩ := exists_rat_gt x,
  exact ⟨r, hr.le⟩,
end

lemma real.Inter_Iic_rat : (⋂ r : ℚ, Iic (r : ℝ)) = ∅ :=
begin
  ext1,
  simp only [mem_Inter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le],
  exact exists_rat_lt x,
end

lemma real.Union_Iic_nat : (⋃ r : ℕ, Iic (r : ℝ)) = univ :=
begin
  ext1,
  simp only [mem_Union, mem_Iic, mem_univ, iff_true],
  obtain ⟨r, hr⟩ := exists_nat_gt x,
  exact ⟨r, hr.le⟩,
end

lemma infi_Ioi_eq_infi_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : bdd_below (f '' Ioi x))
  (hf_mono : monotone f) :
  (⨅ r : Ioi x, f r) = ⨅ q : {q' : ℚ // x < q'}, f q :=
begin
  refine le_antisymm _ _,
  { haveI : nonempty {r' : ℚ // x < ↑r'},
    { obtain ⟨r, hrx⟩ := exists_rat_gt x,
      exact ⟨⟨r, hrx⟩⟩, },
    refine le_cinfi (λ r, _),
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop,
    refine cinfi_set_le hf (hxy.trans _),
    exact_mod_cast hyr, },
  { refine le_cinfi (λ q, _),
    have hq := q.prop,
    rw mem_Ioi at hq,
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq,
    refine (cinfi_le _ _).trans _,
    { exact ⟨y, hxy⟩, },
    { refine ⟨hf.some, λ z, _⟩,
      rintros ⟨u, rfl⟩,
      suffices hfu : f u ∈ f '' Ioi x, from hf.some_spec hfu,
      exact ⟨u, u.prop, rfl⟩, },
    { refine hf_mono (le_trans _ hyq.le),
      norm_cast, }, },
end

lemma lintegral_sub' {m : measurable_space α} {μ : measure α} {f g : α → ℝ≥0∞}
  (hg : ae_measurable g μ) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
begin
  refine ennreal.eq_sub_of_add_eq hg_fin _,
  rw [← lintegral_add_right' _ hg],
  exact lintegral_congr_ae (h_le.mono $ λ x hx, tsub_add_cancel_of_le hx)
end

lemma ennreal.tendsto_at_top_at_bot [nonempty ι] [semilattice_sup ι]
  {f : ι → ℝ≥0∞} (h : tendsto f at_top at_bot) :
  tendsto f at_top (𝓝 0) :=
begin
  rw tendsto_at_bot at h,
  specialize h 0,
  rw eventually_at_top at h,
  obtain ⟨i, hi⟩ := h,
  rw ennreal.tendsto_at_top_zero,
  exact λ ε hε, ⟨i, λ n hn, (hi n hn).trans (zero_le _)⟩,
end

lemma tendsto_of_antitone {ι α : Type*} [preorder ι] [topological_space α]
  [conditionally_complete_linear_order α] [order_topology α] {f : ι → α} (h_mono : antitone f) :
  tendsto f at_top at_bot ∨ (∃ l, tendsto f at_top (𝓝 l)) :=
@tendsto_of_monotone ι αᵒᵈ _ _ _ _ _ h_mono

lemma tendsto_at_top_at_bot_iff_of_antitone [nonempty α] [semilattice_sup α] [preorder β]
  {f : α → β} (hf : antitone f) :
  tendsto f at_top at_bot ↔ ∀ b : β, ∃ a : α, f a ≤ b :=
@tendsto_at_top_at_top_iff_of_monotone α βᵒᵈ _ _ _ _ hf

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
  lift f to α → ℝ≥0 using hf,
  simp_rw [← with_top.coe_infi, ennreal.coe_to_real, nnreal.coe_infi],
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
  borel ℝ = measurable_space.generate_from {S : set ℝ | ∃ (u : ℚ), Iic ↑u = S} :=
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

end aux_lemmas_to_be_moved

namespace measure_theory.measure

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β} {ρ : measure (α × β)}

include mα mβ

/-- Marginal measure on `α` obtained from a measure on `α × β`. -/
noncomputable
def fst (ρ : measure (α × β)) : measure α := ρ.map prod.fst

lemma fst_apply (ρ : measure (α × β)) {s : set α} (hs : measurable_set s) :
  ρ.fst s = ρ (prod.fst ⁻¹' s) :=
by rw [fst, measure.map_apply measurable_fst hs]

lemma fst_univ (ρ : measure (α × β)) : ρ.fst univ = ρ univ :=
by rw [fst_apply ρ measurable_set.univ, preimage_univ]

instance [is_finite_measure ρ] : is_finite_measure ρ.fst := by { rw fst, apply_instance, }

instance [is_probability_measure ρ] : is_probability_measure ρ.fst :=
{ measure_univ := by { rw fst_univ, exact measure_univ, } }

/-- Marginal measure on `β` obtained from a measure on `α × β`. -/
noncomputable
def snd (ρ : measure (α × β)) : measure β := ρ.map prod.snd

lemma snd_apply (ρ : measure (α × β)) {s : set β} (hs : measurable_set s) :
  ρ.snd s = ρ (prod.snd ⁻¹' s) :=
by rw [snd, measure.map_apply measurable_snd hs]

lemma snd_univ (ρ : measure (α × β)) : ρ.snd univ = ρ univ :=
by rw [snd_apply ρ measurable_set.univ, preimage_univ]

instance [is_finite_measure ρ] : is_finite_measure ρ.snd := by { rw snd, apply_instance, }

instance [is_probability_measure ρ] : is_probability_measure ρ.snd :=
{ measure_univ := by { rw snd_univ, exact measure_univ, } }

omit mβ

/-- Measure on such that for a measurable set `s`, `ρ.Iic_snd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable
def Iic_snd (ρ : measure (α × ℝ)) (r : ℚ) : measure α :=
measure.of_measurable (λ s hs, ρ (s ×ˢ Iic r))
  (by simp only [empty_prod, measure_empty])
  (λ f hf_meas hf_disj,
    begin
      rw [set.Union_prod_const, measure_Union],
      { intros i j hij,
        rw [function.on_fun, disjoint_prod],
        exact or.inl (hf_disj hij), },
      { exact λ i, measurable_set.prod (hf_meas i) measurable_set_Iic, }
    end)

lemma Iic_snd_apply (ρ : measure (α × ℝ)) (r : ℚ) {s : set α} (hs : measurable_set s) :
  ρ.Iic_snd r s = ρ (s ×ˢ Iic r) :=
measure.of_measurable_apply s hs

lemma Iic_snd_univ (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r univ = ρ (univ ×ˢ Iic r) :=
Iic_snd_apply ρ r measurable_set.univ

lemma Iic_snd_mono (ρ : measure (α × ℝ)) {r r' : ℚ} (h_le : r ≤ r') :
  ρ.Iic_snd r ≤ ρ.Iic_snd r' :=
begin
  intros s hs,
  simp_rw Iic_snd_apply ρ _ hs,
  refine measure_mono (λ x hx, _),
  simp only [mem_preimage, mem_prod, mem_Iic] at hx ⊢,
  refine ⟨hx.1, hx.2.trans _⟩,
  exact_mod_cast h_le,
end

lemma Iic_snd_le_fst (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r ≤ ρ.fst :=
begin
  intros s hs,
  simp_rw [fst_apply _ hs, Iic_snd_apply ρ r hs],
  refine measure_mono (λ x hx, _),
  simp only [mem_preimage, mem_prod, mem_Iic] at hx ⊢,
  exact hx.1,
end

lemma Iic_snd_ac_fst (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r ≪ ρ.fst :=
measure.absolutely_continuous_of_le (Iic_snd_le_fst ρ r)

instance {ρ : measure (α × ℝ)} [is_finite_measure ρ] (r : ℚ) : is_finite_measure (ρ.Iic_snd r) :=
is_finite_measure_of_le _ (Iic_snd_le_fst ρ _)

lemma infi_Iic_snd_gt (ρ : measure (α × ℝ)) (t : ℚ) {s : set α} (hs : measurable_set s)
  [is_finite_measure ρ] :
  (⨅ r : {r' : ℚ // t < r'}, ρ.Iic_snd r s) = ρ.Iic_snd t s :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs],
  rw ← measure_Inter_eq_infi,
  { congr,
    ext1 x,
    simp only [coe_coe, mem_Inter, mem_prod, mem_Iic, subtype.forall, subtype.coe_mk],
    refine ⟨λ h, _, λ h a hta, ⟨h.1, h.2.trans _⟩⟩,
    { refine ⟨(h (t+1) (lt_add_one _)).1, le_of_forall_lt_rat_imp_le (λ q htq, (h q _).2)⟩,
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

lemma tendsto_Iic_snd_at_top (ρ : measure (α × ℝ)) {s : set α} (hs : measurable_set s) :
  tendsto (λ r, ρ.Iic_snd r s) at_top (𝓝 (ρ.fst s)) :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs, fst_apply ρ hs, ← prod_univ],
  rw [← real.Union_Iic_rat, prod_Union],
  refine tendsto_measure_Union (λ r q hr_le_q x, _),
  simp only [mem_prod, mem_Iic, and_imp],
  refine λ hxs hxr, ⟨hxs, hxr.trans _⟩,
  exact_mod_cast hr_le_q,
end

lemma tendsto_Iic_snd_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  tendsto (λ r, ρ.Iic_snd r s) at_bot (𝓝 0) :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs],
  have h_empty : ρ (s ×ˢ ∅) = 0,
  { simp only [prod_empty, measure_empty], },
  rw [← h_empty, ← real.Inter_Iic_rat, prod_Inter],
  suffices h_neg : tendsto (λ r : ℚ, ρ (s ×ˢ Iic (↑-r))) at_top (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic (↑-r)))),
  { have h_inter_eq : (⋂ r : ℚ, s ×ˢ Iic (↑-r)) = (⋂ r : ℚ, s ×ˢ Iic (r : ℝ)),
    { ext1 x,
      simp only [rat.cast_eq_id, id.def, mem_Inter, mem_prod, mem_Iic],
      refine ⟨λ h i, ⟨(h i).1, _⟩, λ h i, ⟨(h i).1, _⟩⟩; have h' := h (-i),
      { rw neg_neg at h', exact h'.2, },
      { exact h'.2, }, },
    rw h_inter_eq at h_neg,
    have h_fun_eq : (λ (r : ℚ), ρ (s ×ˢ Iic (r : ℝ))) = (λ r, ρ (s ×ˢ Iic ↑(- -r))),
    { simp_rw neg_neg, },
    rw h_fun_eq,
    exact h_neg.comp tendsto_neg_at_bot_at_top, },
  refine tendsto_measure_Inter (λ q, hs.prod measurable_set_Iic) _ ⟨0, measure_ne_top ρ _⟩,
  intros q r hqr x,
  simp only [mem_prod, mem_Iic, and_imp, rat.cast_neg],
  refine λ hxs hxr, ⟨hxs, hxr.trans (neg_le_neg _)⟩,
  exact_mod_cast hqr,
end

end measure_theory.measure

open measure_theory

namespace probability_theory

variables {α β ι : Type*} {mα : measurable_space α}

include mα

noncomputable
def pre_cdf (ρ : measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ := measure.rn_deriv (ρ.Iic_snd r) ρ.fst

lemma measurable_pre_cdf {ρ : measure (α × ℝ)} {r : ℚ} : measurable (pre_cdf ρ r) :=
measure.measurable_rn_deriv _ _

lemma with_density_pre_cdf (ρ : measure (α × ℝ)) (r : ℚ) [is_finite_measure ρ] :
  ρ.fst.with_density (pre_cdf ρ r) = ρ.Iic_snd r :=
measure.absolutely_continuous_iff_with_density_rn_deriv_eq.mp (measure.Iic_snd_ac_fst ρ r)

lemma set_lintegral_pre_cdf_fst (ρ : measure (α × ℝ)) (r : ℚ) {s : set α}
  (hs : measurable_set s) [is_finite_measure ρ] :
  ∫⁻ x in s, pre_cdf ρ r x ∂ρ.fst = ρ.Iic_snd r s :=
begin
  have : ∀ r, ∫⁻ x in s, pre_cdf ρ r x ∂ρ.fst = ∫⁻ x in s, (pre_cdf ρ r * 1) x ∂ρ.fst,
  { simp only [mul_one, eq_self_iff_true, forall_const], },
  rw [this, ← set_lintegral_with_density_eq_set_lintegral_mul _ _ _ hs],
  { rw with_density_pre_cdf ρ r,
    simp only [pi.one_apply, lintegral_one, measure.restrict_apply, measurable_set.univ,
      univ_inter], },
  { exact measurable_pre_cdf, },
  { rw (_ : (1 : α → ℝ≥0∞) = (λ _, 1)),
    { exact measurable_const, },
    { refl, }, },
end

lemma monotone_pre_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, monotone (λ r, pre_cdf ρ r a) :=
begin
  simp_rw [monotone, ae_all_iff],
  intros r r' hrr',
  refine ae_le_of_forall_set_lintegral_le_of_sigma_finite measurable_pre_cdf measurable_pre_cdf _,
  intros s hs hs_fin,
  rw [set_lintegral_pre_cdf_fst ρ r hs, set_lintegral_pre_cdf_fst ρ r' hs],
  refine measure.Iic_snd_mono ρ _ s hs,
  exact_mod_cast hrr',
end

lemma set_lintegral_infi_gt_pre_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] (t : ℚ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ x in s, ⨅ r : Ioi t, pre_cdf ρ r x ∂ρ.fst = ρ.Iic_snd t s :=
begin
  refine le_antisymm _ _,
  { have h : ∀ q : Ioi t, ∫⁻ x in s, ⨅ r : Ioi t, pre_cdf ρ r x ∂ρ.fst ≤ ρ.Iic_snd q s,
    { intros q,
      calc ∫⁻ x in s, ⨅ r : Ioi t, pre_cdf ρ r x ∂ρ.fst
          ≤ ∫⁻ x in s, pre_cdf ρ q x ∂ρ.fst :
        begin
          refine set_lintegral_mono_ae _ measurable_pre_cdf _,
          { exact measurable_infi (λ _, measurable_pre_cdf), },
          { filter_upwards [monotone_pre_cdf] with a ha_mono,
            exact λ _, infi_le _ q, },
        end
      ... = ρ.Iic_snd q s : set_lintegral_pre_cdf_fst ρ _ hs, },
    calc ∫⁻ x in s, (⨅ (r : Ioi t), pre_cdf ρ r x) ∂ρ.fst
        ≤ ⨅ q : Ioi t, ρ.Iic_snd q s : le_infi h
    ... = ρ.Iic_snd t s : measure.infi_Iic_snd_gt ρ t hs, },
  { calc ρ.Iic_snd t s
      = ∫⁻ x in s, pre_cdf ρ t x ∂ρ.fst : (set_lintegral_pre_cdf_fst ρ t hs).symm
  ... ≤ ∫⁻ x in s, ⨅ (r : Ioi t), pre_cdf ρ ↑r x ∂ρ.fst :
    begin
      refine set_lintegral_mono_ae measurable_pre_cdf _ _,
      { refine measurable_infi (λ _, measurable_pre_cdf), },
      { filter_upwards [monotone_pre_cdf] with a ha_mono,
        exact λ _, le_infi (λ r, ha_mono (le_of_lt r.prop)), },
    end, },
end

lemma pre_cdf_le_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, ∀ r, pre_cdf ρ r a ≤ 1 :=
begin
  rw ae_all_iff,
  refine λ r, ae_le_of_forall_set_lintegral_le_of_sigma_finite measurable_pre_cdf
    measurable_const (λ s hs hs_fin, _),
  rw set_lintegral_pre_cdf_fst ρ r hs,
  simp only [pi.one_apply, lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
  exact measure.Iic_snd_le_fst ρ r s hs,
end

lemma tendsto_lintegral_pre_cdf_at_top (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top (𝓝 (ρ univ)) :=
begin
  suffices : tendsto (λ r, ρ.Iic_snd r univ) at_top (𝓝 (ρ.fst univ)),
  { convert this,
    { ext1 r,
      rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ], },
    { exact (measure.fst_univ ρ).symm }, },
  exact ρ.tendsto_Iic_snd_at_top measurable_set.univ,
end

lemma tendsto_lintegral_pre_cdf_at_top' (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top (𝓝 (∫⁻ a, 1 ∂ρ.fst)) :=
by { convert tendsto_lintegral_pre_cdf_at_top ρ, rw [lintegral_one, measure.fst_univ], }

lemma tendsto_lintegral_pre_cdf_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_bot (𝓝 0) :=
begin
  suffices : tendsto (λ r, ρ.Iic_snd r univ) at_bot (𝓝 0),
  { convert this,
    ext1 r,
    rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ], },
  exact ρ.tendsto_Iic_snd_at_bot measurable_set.univ,
end

lemma tendsto_pre_cdf_at_top_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 1) :=
begin
  have h_mono := monotone_pre_cdf ρ,
  have h_le_one := pre_cdf_le_one ρ,
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l ≤ (1 : ℝ≥0∞), tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l),
  { filter_upwards [h_mono, h_le_one] with a ha_mono ha_le_one,
    -- todo: no direct way to get the or.inr of this?
    have h_tendsto : tendsto (λ r, pre_cdf ρ r a) at_top at_top
      ∨ ∃ l, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l) := tendsto_of_monotone ha_mono,
    cases h_tendsto with h_absurd h_tendsto,
    { rw monotone.tendsto_at_top_at_top_iff ha_mono at h_absurd,
      obtain ⟨r, hr⟩ := h_absurd 2,
      exact absurd (hr.trans (ha_le_one r)) ennreal.one_lt_two.not_le, },
    obtain ⟨l, hl⟩ := h_tendsto,
    exact ⟨l, le_of_tendsto' hl ha_le_one, hl⟩, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l ≤ (1 : ℝ≥0∞), tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l) then h.some else 0,
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec.some_spec },
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, tendsto (λ n : ℕ, pre_cdf ρ n a) at_top (𝓝 (F a)),
  { filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_coe_nat_at_top_at_top, },
  have hF_ae_meas : ae_measurable F ρ.fst,
  { refine ae_measurable_of_tendsto_metrizable_ae' (λ n, _) h_tendsto_ℕ,
    exact measurable_pre_cdf.ae_measurable, },
  have hF_le_one : ∀ᵐ a ∂ρ.fst, F a ≤ 1,
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec.some, },
  suffices : ∀ᵐ a ∂ρ.fst, F a = 1,
  { filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  have h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = ∫⁻ a, 1 ∂ρ.fst,
  { have h_lintegral : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top
      (𝓝 (∫⁻ a, F a ∂ρ.fst)),
    { refine lintegral_tendsto_of_tendsto_of_monotone
        (λ _, measurable_pre_cdf.ae_measurable) _ h_tendsto_ℕ,
      filter_upwards [h_mono] with a ha,
      refine λ n m hnm, ha _,
      exact_mod_cast hnm, },
    have h_lintegral' : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top
      (𝓝 (∫⁻ a, 1 ∂ρ.fst)),
    { exact (tendsto_lintegral_pre_cdf_at_top' ρ).comp tendsto_coe_nat_at_top_at_top, },
    exact tendsto_nhds_unique h_lintegral h_lintegral', },
  have : ∫⁻ a, (1 - F a) ∂ρ.fst = 0,
  { rw [lintegral_sub' hF_ae_meas _ hF_le_one, h_lintegral_eq, tsub_self],
    calc ∫⁻ a, F a ∂ρ.fst = ∫⁻ a, 1 ∂ρ.fst : h_lintegral_eq
    ... = ρ.fst univ : lintegral_one
    ... = ρ univ : measure.fst_univ ρ
    ... ≠ ⊤ : measure_ne_top ρ _, },
  rw lintegral_eq_zero_iff' at this,
  { filter_upwards [this, hF_le_one] with ha h_one_sub_eq_zero h_le_one,
    rw [pi.zero_apply, tsub_eq_zero_iff_le] at h_one_sub_eq_zero,
    exact le_antisymm h_le_one h_one_sub_eq_zero, },
  { exact ae_measurable_const.sub hF_ae_meas, },
end

lemma tendsto_pre_cdf_at_bot_zero (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_bot (𝓝 0) :=
begin
  suffices : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 0),
  { filter_upwards [this] with a ha,
    have h_eq_neg : (λ (r : ℚ), pre_cdf ρ r a) = (λ (r : ℚ), pre_cdf ρ (- -r) a),
    { simp_rw neg_neg, },
    rw h_eq_neg,
    exact ha.comp tendsto_neg_at_bot_at_top, },
  have h_mono := monotone_pre_cdf ρ,
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l),
  { filter_upwards [h_mono] with a ha,
    have h_anti : antitone (λ r, pre_cdf ρ (-r) a) := λ p q hpq, ha (neg_le_neg hpq),
    have h_tendsto : tendsto (λ r, pre_cdf ρ (-r) a) at_top at_bot
      ∨ ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l) := tendsto_of_antitone h_anti,
    cases h_tendsto with h_bot h_tendsto,
    { exact ⟨0, ennreal.tendsto_at_top_at_bot h_bot⟩, },
    { exact h_tendsto, }, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l) then h.some else 0,
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec, },
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, tendsto (λ n : ℕ, pre_cdf ρ (-n) a) at_top (𝓝 (F a)),
  { filter_upwards [h_tendsto_ℚ] with a ha,
    exact ha.comp tendsto_coe_nat_at_top_at_top, },
  have hF_ae_meas : ae_measurable F ρ.fst,
  { refine ae_measurable_of_tendsto_metrizable_ae' (λ n, _) h_tendsto_ℕ,
    exact measurable_pre_cdf.ae_measurable, },
  suffices : ∀ᵐ a ∂ρ.fst, F a = 0,
  { filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  suffices h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = 0,
  { rwa [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq, },
  have h_lintegral : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) at_top
    (𝓝 (∫⁻ a, F a ∂ρ.fst)),
  { refine tendsto_lintegral_of_dominated_convergence (λ _, 1) (λ _, measurable_pre_cdf) (λ _, _)
      _ h_tendsto_ℕ,
    { filter_upwards [pre_cdf_le_one ρ] with a ha using ha _, },
    { rw lintegral_one,
      exact measure_ne_top _ _, }, },
  have h_lintegral' : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) at_top
    (𝓝 0),
  { have h_lintegral_eq : (λ r : ℕ, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) = λ r, ρ (univ ×ˢ Iic (-r)),
    { ext1 n,
      rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ,
        measure.Iic_snd_univ],
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
  exact tendsto_nhds_unique h_lintegral h_lintegral',
end

lemma inf_gt_pre_cdf_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, ∀ t : ℚ, (⨅ r : Ioi t, pre_cdf ρ r a) = pre_cdf ρ t a :=
begin
  rw ae_all_iff,
  refine λ t, ae_eq_of_forall_set_lintegral_eq_of_sigma_finite _ measurable_pre_cdf _,
  { exact measurable_infi (λ i, measurable_pre_cdf), },
  intros s hs hs_fin,
  rw [set_lintegral_infi_gt_pre_cdf ρ t hs, set_lintegral_pre_cdf_fst ρ t hs],
end


open_locale classical


section has_cond_cdf

/-- A product measure on `α × ℝ` is said to have a conditional cdf at `a : α` if `pre_cdf` is
monotone with limit 0 at -∞ and 1 at +∞, and is right continuous. -/
def has_cond_cdf (ρ : measure (α × ℝ)) (a : α) : Prop :=
monotone (λ r, pre_cdf ρ r a) ∧ (∀ r, pre_cdf ρ r a ≤ 1)
  ∧ (tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 1)) ∧ (tendsto (λ r, pre_cdf ρ r a) at_bot (𝓝 0))
  ∧ (∀ t : ℚ, (⨅ r : Ioi t, pre_cdf ρ r a) = pre_cdf ρ t a)

lemma has_cond_cdf_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, has_cond_cdf ρ a :=
begin
  simp_rw [has_cond_cdf, eventually_and],
  exact ⟨monotone_pre_cdf ρ, pre_cdf_le_one ρ, tendsto_pre_cdf_at_top_one ρ,
    tendsto_pre_cdf_at_bot_zero ρ, inf_gt_pre_cdf_ae_eq ρ⟩,
end

/-- A measurable set of elements of `α` such that `ρ` has a conditional cdf at all
`a ∈ cond_cdf_set`. -/
def cond_cdf_set (ρ : measure (α × ℝ)) : set α :=
(to_measurable ρ.fst {b | ¬ has_cond_cdf ρ b})ᶜ

lemma measurable_set_cond_cdf_set (ρ : measure (α × ℝ)) : measurable_set (cond_cdf_set ρ) :=
(measurable_set_to_measurable _ _).compl

lemma has_cond_cdf_of_mem_cond_cdf_set {ρ : measure (α × ℝ)} {a : α} (h : a ∈ cond_cdf_set ρ) :
  has_cond_cdf ρ a :=
begin
  rw [cond_cdf_set, mem_compl_iff] at h,
  have h_ss := subset_to_measurable ρ.fst {b | ¬ has_cond_cdf ρ b},
  by_contra ha,
  exact h (h_ss ha),
end

lemma cond_cdf_set_subset (ρ : measure (α × ℝ)) :
  cond_cdf_set ρ ⊆ {a | has_cond_cdf ρ a} :=
λ x, has_cond_cdf_of_mem_cond_cdf_set

lemma fst_compl_cond_cdf_set (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ρ.fst (cond_cdf_set ρ)ᶜ = 0 :=
by { rw [cond_cdf_set, compl_compl, measure_to_measurable], exact has_cond_cdf_ae ρ, }

lemma mem_cond_cdf_set_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, a ∈ cond_cdf_set ρ :=
fst_compl_cond_cdf_set ρ

end has_cond_cdf


/-- Conditional cdf of the measure on the `ℝ` given the value on `α`. It is defined to be `pre_cdf`
if it verifies a list of properties, and a default cdf-like function otherwise. -/
noncomputable
def cond_cdf_rat (ρ : measure (α × ℝ)) : α → ℚ → ℝ :=
λ a, if a ∈ cond_cdf_set ρ then (λ r, (pre_cdf ρ r a).to_real) else (λ r, if r < 0 then 0 else 1)

lemma cond_cdf_rat_of_not_mem (ρ : measure (α × ℝ)) (a : α) (h : a ∉ cond_cdf_set ρ) {r : ℚ} :
  cond_cdf_rat ρ a r = if r < 0 then 0 else 1 :=
by simp only [cond_cdf_rat, h, if_false]

lemma cond_cdf_rat_of_mem (ρ : measure (α × ℝ)) (a : α) (h : a ∈ cond_cdf_set ρ) (r : ℚ) :
  cond_cdf_rat ρ a r = (pre_cdf ρ r a).to_real :=
by simp only [cond_cdf_rat, h, if_true]

lemma monotone_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) :
  monotone (cond_cdf_rat ρ a) :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { simp only [cond_cdf_rat, h, if_true, forall_const, and_self],
    intros r r' hrr',
    have h' := has_cond_cdf_of_mem_cond_cdf_set h,
    have h_ne_top : ∀ r, pre_cdf ρ r a ≠ ∞ := λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne,
    rw ennreal.to_real_le_to_real (h_ne_top _) (h_ne_top _),
    exact h'.1 hrr', },
  { simp only [cond_cdf_rat, h, if_false],
    intros x y hxy,
    dsimp only,
    split_ifs,
    exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl], },
end

lemma measurable_cond_cdf_rat (ρ : measure (α × ℝ)) (q : ℚ) :
  measurable (λ a, cond_cdf_rat ρ a q) :=
begin
  rw cond_cdf_rat,
  simp_rw ite_apply,
  refine measurable.ite (measurable_set_cond_cdf_set ρ) _ measurable_const,
  exact measurable_pre_cdf.ennreal_to_real,
end

lemma cond_cdf_rat_nonneg (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  0 ≤ cond_cdf_rat ρ a r :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { rw cond_cdf_rat_of_mem _ _ h,
    exact ennreal.to_real_nonneg, },
  { rw cond_cdf_rat_of_not_mem _ _ h,
    split_ifs,
    { refl, },
    { exact zero_le_one, }, },
end

lemma cond_cdf_rat_le_one (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_cdf_rat ρ a r ≤ 1 :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { have h' := has_cond_cdf_of_mem_cond_cdf_set h,
    rw cond_cdf_rat_of_mem _ _ h,
    refine ennreal.to_real_le_of_le_of_real zero_le_one _,
    rw ennreal.of_real_one,
    exact h'.2.1 r, },
  { rw cond_cdf_rat_of_not_mem _ _ h,
    split_ifs,
    exacts [zero_le_one, le_rfl], },
end

lemma tendsto_cond_cdf_rat_at_bot (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf_rat ρ a) at_bot (𝓝 0) :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { simp only [cond_cdf_rat, h, if_true],
    rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff],
    { exact (has_cond_cdf_of_mem_cond_cdf_set h).2.2.2.1, },
    { have h' := has_cond_cdf_of_mem_cond_cdf_set h,
      exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.zero_ne_top, }, },
  { simp only [cond_cdf_rat, h, if_false],
    refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_bot],
    refine ⟨-1, λ q hq, _⟩,
    rw if_pos,
    refine hq.trans_lt _,
    linarith, },
end

lemma tendsto_cond_cdf_rat_at_top (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf_rat ρ a) at_top (𝓝 1) :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { simp only [cond_cdf_rat, h, if_true],
    rw [← ennreal.one_to_real, ennreal.tendsto_to_real_iff],
    { exact (has_cond_cdf_of_mem_cond_cdf_set h).2.2.1, },
    { have h' := has_cond_cdf_of_mem_cond_cdf_set h,
      exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.one_ne_top, }, },
  { simp only [cond_cdf_rat, h, if_false],
    refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_top],
    refine ⟨0, λ q hq, _⟩,
    rw if_neg,
    exact not_lt.mpr hq, },
end

lemma cond_cdf_rat_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, cond_cdf_rat ρ a r) =ᵐ[ρ.fst] λ a, (pre_cdf ρ r a).to_real :=
by filter_upwards [mem_cond_cdf_set_ae ρ] with a ha using cond_cdf_rat_of_mem ρ a ha r

lemma of_real_cond_cdf_rat_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, ennreal.of_real (cond_cdf_rat ρ a r)) =ᵐ[ρ.fst] pre_cdf ρ r :=
begin
  filter_upwards [cond_cdf_rat_ae_eq ρ r, pre_cdf_le_one ρ] with a ha ha_le_one,
  rw [ha, ennreal.of_real_to_real],
  exact ((ha_le_one r).trans_lt ennreal.one_lt_top).ne,
end

lemma cond_cdf_rat_eq_inf_gt (ρ : measure (α × ℝ)) (a : α) (t : ℚ) :
  (⨅ r : Ioi t, cond_cdf_rat ρ a r) = cond_cdf_rat ρ a t :=
begin
  by_cases ha : a ∈ cond_cdf_set ρ,
  { simp_rw cond_cdf_rat_of_mem ρ a ha,
    have ha' := has_cond_cdf_of_mem_cond_cdf_set ha,
    rw ← to_real_infi,
    { suffices : (⨅ (i : ↥(Ioi t)), pre_cdf ρ ↑i a) = pre_cdf ρ t a, by rw this,
      rw ← ha'.2.2.2.2, },
    { exact λ r, ((ha'.2.1 r).trans_lt ennreal.one_lt_top).ne, }, },
  { simp_rw cond_cdf_rat_of_not_mem ρ a ha,
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
def cond_cdf (ρ : measure (α × ℝ)) : α → ℝ → ℝ :=
λ a t, ⨅ r : {r' : ℚ // t < r'}, cond_cdf_rat ρ a r

lemma cond_cdf_eq_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_cdf ρ a r = cond_cdf_rat ρ a r :=
begin
  rw [← cond_cdf_rat_eq_inf_gt ρ a r, cond_cdf],
  refine equiv.infi_congr _ _,
  { exact
    { to_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      inv_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      left_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta],
      right_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta], }, },
  { intro t,
    simp only [subtype.val_eq_coe, equiv.coe_fn_mk, subtype.coe_mk], },
end

lemma monotone_cond_cdf (ρ : measure (α × ℝ)) (a : α) : monotone (cond_cdf ρ a) :=
begin
  intros x y hxy,
  rw [cond_cdf],
  haveI : nonempty {r' : ℚ // y < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt y,
    exact ⟨⟨r, hrx⟩⟩, },
  refine le_cinfi (λ r, _),
  have hxr : x < r := hxy.trans_lt r.prop,
  refine (cinfi_le _ _).trans_eq _,
  { exact ⟨r.1, hxr⟩, },
  { refine ⟨0, λ z, _⟩,
    rintros ⟨u, rfl⟩,
    exact cond_cdf_rat_nonneg ρ a _, },
  { refl, },
end

lemma cond_cdf_nonneg (ρ : measure (α × ℝ)) (a : α) (r : ℝ) :
  0 ≤ cond_cdf ρ a r :=
begin
  haveI : nonempty {r' : ℚ // r < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt r,
    exact ⟨⟨r, hrx⟩⟩, },
  exact le_cinfi (λ r', cond_cdf_rat_nonneg ρ a _),
end

lemma tendsto_cond_cdf_Ioi (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  tendsto (cond_cdf ρ a) (𝓝[Ioi x] x) (𝓝 (cond_cdf ρ a x)) :=
begin
  convert monotone.tendsto_nhds_within_Ioi (monotone_cond_cdf ρ a) x,
  rw Inf_image',
  have h' : (⨅ r : Ioi x, cond_cdf ρ a r) = ⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a r,
  { refine infi_Ioi_eq_infi_rat_gt x _ (monotone_cond_cdf ρ a),
    refine ⟨0, λ z, _⟩,
    rintros ⟨u, hux, rfl⟩,
    exact cond_cdf_nonneg ρ a u, },
  have h'' : (⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a r)
    = ⨅ r : {r' : ℚ // x < r'}, cond_cdf_rat ρ a r,
  { congr' with r,
    exact cond_cdf_eq_cond_cdf_rat ρ a r, },
  rw [h', h''],
  refl,
end

lemma continuous_within_at_cond_cdf (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  continuous_within_at (cond_cdf ρ a) (Ici x) x :=
by { rw ← continuous_within_at_Ioi_iff_Ici, exact tendsto_cond_cdf_Ioi ρ a x, }

/-- Conditional cdf as a Stieltjes function. -/
noncomputable
def cond_cdf_stieltjes (ρ : measure (α × ℝ)) (a : α) : stieltjes_function :=
{ to_fun := cond_cdf ρ a,
  mono' := monotone_cond_cdf ρ a,
  right_continuous' := continuous_within_at_cond_cdf ρ a }

/-- Conditional measure on the second space of the product given the value on the first. -/
noncomputable
def cond_measure (ρ : measure (α × ℝ)) (a : α) : measure ℝ :=
(cond_cdf_stieltjes ρ a).measure

lemma cond_measure_Ioc (ρ : measure (α × ℝ)) (a : α) (q q' : ℚ) :
  cond_measure ρ a (Ioc q q') = ennreal.of_real (cond_cdf_rat ρ a q' - cond_cdf_rat ρ a q) :=
begin
  rw [cond_measure, stieltjes_function.measure_Ioc, ← cond_cdf_eq_cond_cdf_rat,
    ← cond_cdf_eq_cond_cdf_rat],
  refl,
end

lemma cond_measure_Iic (ρ : measure (α × ℝ)) (a : α) (q : ℚ) :
  cond_measure ρ a (Iic q) = ennreal.of_real (cond_cdf_rat ρ a q) :=
begin
  have h_tendsto_1 : tendsto (λ r : ℚ, cond_measure ρ a (Ioc r q)) at_bot
    (𝓝 (cond_measure ρ a (Iic q))),
  { have h_Iic_eq_Union : Iic (q : ℝ) = ⋃ r : ℚ, Ioc (↑-r) q,
    { ext1 x,
      simp only [mem_Iic, mem_Union, mem_Ioc, exists_and_distrib_right, iff_and_self],
      intro h,
      simp_rw [rat.cast_neg, neg_lt],
      exact exists_rat_gt _, },
    rw h_Iic_eq_Union,
    suffices h_neg_top : tendsto (λ (r : ℚ), cond_measure ρ a (Ioc (↑-r) q)) at_top
      (𝓝 (cond_measure ρ a (⋃ (r : ℚ), Ioc (↑-r) q))),
    { have : (λ (r : ℚ), cond_measure ρ a (Ioc (↑r) q)) = (λ r, cond_measure ρ a (Ioc (↑-(-r)) q)),
      { simp_rw neg_neg, },
      rw this,
      exact h_neg_top.comp tendsto_neg_at_bot_at_top, },
    refine tendsto_measure_Union (λ r r' hrr' x, _),
    simp only [rat.cast_neg, mem_Ioc, and_imp],
    refine λ hrx hxq, ⟨(neg_le_neg _).trans_lt hrx, hxq⟩,
    exact_mod_cast hrr', },
  have h_tendsto_2 :tendsto (λ r : ℚ, cond_measure ρ a (Ioc r q)) at_bot
    (𝓝 (ennreal.of_real (cond_cdf_rat ρ a q))),
  { simp_rw cond_measure_Ioc,
    refine ennreal.tendsto_of_real _,
    nth_rewrite 0 ← sub_zero (cond_cdf_rat ρ a q),
    refine tendsto.const_sub _ _,
    exact tendsto_cond_cdf_rat_at_bot ρ a, },
  exact tendsto_nhds_unique h_tendsto_1 h_tendsto_2,
end

lemma cond_measure_univ (ρ : measure (α × ℝ)) (a : α) :
  cond_measure ρ a univ = 1 :=
begin
  have h_tendsto1 :
    tendsto (λ q : ℚ, cond_measure ρ a (Iic q)) at_top (𝓝 (cond_measure ρ a univ)),
  { rw ← real.Union_Iic_rat,
    refine tendsto_measure_Union (λ r q hr_le_q x, _),
    simp only [mem_Iic],
    refine λ hxr, hxr.trans _,
    exact_mod_cast hr_le_q, },
  have h_tendsto2 :
    tendsto (λ q : ℚ, cond_measure ρ a (Iic q)) at_top (𝓝 1),
  { simp_rw cond_measure_Iic ρ a,
    rw ← ennreal.of_real_one,
    refine ennreal.tendsto_of_real _,
    exact tendsto_cond_cdf_rat_at_top ρ a, },
  exact tendsto_nhds_unique h_tendsto1 h_tendsto2,
end

instance (ρ : measure (α × ℝ)) (a : α) : is_probability_measure (cond_measure ρ a) :=
⟨cond_measure_univ ρ a⟩

lemma measurable_cond_measure (ρ : measure (α × ℝ)) :
  measurable (cond_measure ρ) :=
begin
  rw measure.measurable_measure,
  refine λ s hs, measurable_space.induction_on_inter
    borel_eq_generate_from_Iic_rat is_pi_system_Iic_rat _ _ _ _ hs,
  { simp only [measure_empty, measurable_const], },
  { rintros S ⟨u, rfl⟩,
    simp_rw cond_measure_Iic ρ _ u,
    exact (measurable_cond_cdf_rat ρ u).ennreal_of_real, },
  { intros t ht ht_cd_meas,
    have : (λ a, cond_measure ρ a tᶜ) = (λ a, cond_measure ρ a univ) - (λ a, cond_measure ρ a t),
    { ext1 a,
      rw [measure_compl ht (measure_ne_top (cond_measure ρ a) _), pi.sub_apply], },
    simp_rw [this, cond_measure_univ ρ],
    exact measurable.sub measurable_const ht_cd_meas, },
  { intros f hf_disj hf_meas hf_cd_meas,
    simp_rw measure_Union hf_disj hf_meas,
    exact measurable.ennreal_tsum hf_cd_meas, },
end

noncomputable
def cond_kernel (ρ : measure (α × ℝ)) : kernel α ℝ :=
{ val := λ a, cond_measure ρ a,
  property := measurable_cond_measure ρ }

lemma cond_kernel_apply (ρ : measure (α × ℝ)) (a : α) : cond_kernel ρ a = cond_measure ρ a := rfl

lemma cond_kernel_Iic (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_kernel ρ a (Iic r) = ennreal.of_real (cond_cdf_rat ρ a r) :=
by rw [cond_kernel_apply, cond_measure_Iic ρ]

instance (ρ : measure (α × ℝ)) : is_markov_kernel (cond_kernel ρ) :=
⟨λ a, by { rw cond_kernel, apply_instance, } ⟩

lemma set_lintegral_cond_kernel_Iic_rat (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel ρ a (Iic r) ∂ρ.fst = ρ (s ×ˢ Iic r) :=
begin
  simp_rw [cond_kernel_Iic ρ],
  have : ∀ᵐ a ∂ρ.fst, a ∈ s → ennreal.of_real (cond_cdf_rat ρ a r) = pre_cdf ρ r a,
  { filter_upwards [of_real_cond_cdf_rat_ae_eq ρ r] with a ha using λ _, ha, },
  rw [set_lintegral_congr_fun hs this, set_lintegral_pre_cdf_fst ρ r hs],
  exact ρ.Iic_snd_apply r hs,
end

lemma set_lintegral_cond_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel ρ a univ ∂ρ.fst = ρ (s ×ˢ univ) :=
begin
  have h_univ : univ = ⋃ n : ℕ, Iic (n : ℝ) := real.Union_Iic_nat.symm,
  have h_tendsto1 : tendsto (λ n : ℕ, ∫⁻ a in s, cond_kernel ρ a (Iic n) ∂ρ.fst) at_top
    (𝓝 (∫⁻ a in s, cond_kernel ρ a univ ∂ρ.fst)),
  { rw h_univ,
    refine tendsto_lintegral_of_dominated_convergence (λ _, 1) _ _ _ _,
    { exact λ n, kernel.measurable_coe _ measurable_set_Iic, },
    { refine λ n, eventually_of_forall (λ a, _),
      dsimp only,
      have : (n : ℝ) = ↑(n : ℚ) := rfl,
      rw [this, cond_kernel_Iic, ← ennreal.of_real_one],
      exact ennreal.of_real_le_of_real (cond_cdf_rat_le_one ρ a _), },
    { simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter, ne.def],
      exact measure_ne_top _ _, },
    { refine eventually_of_forall (λ a, tendsto_measure_Union (λ n m hnm x, _)),
      simp only [mem_Iic],
      refine λ hxn, hxn.trans _,
      exact_mod_cast hnm, }, },
  have h_tendsto2 : tendsto (λ n : ℕ, ∫⁻ a in s, cond_kernel ρ a (Iic n) ∂ρ.fst) at_top
    (𝓝 (ρ (s ×ˢ univ))),
  { have : ∀ n : ℕ, (n : ℝ) = ↑(n : ℚ) := λ n, rfl,
    simp_rw [this, set_lintegral_cond_kernel_Iic_rat _ _ hs],
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

lemma lintegral_cond_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∫⁻ a, cond_kernel ρ a univ ∂ρ.fst = ρ univ :=
by rw [← set_lintegral_univ, set_lintegral_cond_kernel_univ ρ measurable_set.univ, univ_prod_univ]

lemma set_lintegral_cond_kernel_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) {t : set ℝ} (ht : measurable_set t) :
  ∫⁻ a in s, cond_kernel ρ a t ∂ρ.fst = ρ (s ×ˢ t) :=
begin
  refine measurable_space.induction_on_inter borel_eq_generate_from_Iic_rat is_pi_system_Iic_rat
    _ _ _ _ ht,
  { simp only [measure_empty, lintegral_const, zero_mul, prod_empty], },
  { rintros t ⟨q, rfl⟩,
    exact set_lintegral_cond_kernel_Iic_rat ρ q hs, },
  { intros t ht ht_lintegral,
    have h_ne_top : ∀ a, cond_kernel ρ a t ≠ ∞ := λ a, measure_ne_top _ _,
    calc ∫⁻ a in s, cond_kernel ρ a tᶜ ∂ρ.fst
        = ∫⁻ a in s, (cond_kernel ρ a univ) - cond_kernel ρ a t ∂ρ.fst :
      by { congr' with a, rw measure_compl ht (h_ne_top _), }
    ... = ∫⁻ a in s, (cond_kernel ρ a univ) ∂ρ.fst - ∫⁻ a in s, cond_kernel ρ a t ∂ρ.fst :
      begin
        rw lintegral_sub,
        { exact kernel.measurable_coe _ ht, },
        { rw ht_lintegral,
          exact measure_ne_top ρ _, },
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
      end
    ... = ρ (s ×ˢ univ) - ρ (s ×ˢ t) : by rw [set_lintegral_cond_kernel_univ ρ hs, ht_lintegral]
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

lemma lintegral_cond_kernel (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set (α × ℝ)} (hs : measurable_set s) :
  ∫⁻ a, cond_kernel ρ a {x | (a, x) ∈ s} ∂ρ.fst = ρ s :=
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
    have h_int_eq : ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst
      = ∫⁻ a in t₁, cond_kernel ρ a t₂ ∂ρ.fst,
    { rw ← lintegral_add_compl _ ht₁,
      have h_eq1 : ∫⁻ a in t₁, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst
        = ∫⁻ a in t₁, cond_kernel ρ a t₂ ∂ρ.fst,
      { refine set_lintegral_congr_fun ht₁ (eventually_of_forall (λ a ha, _)),
        rw h_prod_eq_snd a ha, },
      have h_eq2 : ∫⁻ a in t₁ᶜ, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst = 0,
      { suffices h_eq_zero : ∀ a ∈ t₁ᶜ, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = 0,
        { rw set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero),
          simp only [lintegral_const, zero_mul], },
        intros a hat₁,
        suffices : {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = ∅, by rw [this, measure_empty],
        ext1 x,
        simp only [prod_mk_mem_set_prod_eq, mem_set_of_eq, mem_empty_iff_false, iff_false, not_and],
        exact λ ha, absurd ha hat₁, },
      rw [h_eq1, h_eq2, add_zero], },
    rw h_int_eq,
    exact set_lintegral_cond_kernel_prod ρ ht₁ ht₂, },
  { intros t ht ht_eq,
    calc ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ tᶜ} ∂ρ.fst
        = ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t}ᶜ ∂ρ.fst : rfl
    ... = ∫⁻ a, cond_kernel ρ a univ - cond_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        congr' with a : 1,
        rw measure_compl _ (measure_ne_top (cond_kernel ρ a) _),
        exact measurable_prod_mk_left ht,
      end
    ... = ∫⁻ a, cond_kernel ρ a univ ∂ρ.fst - ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        have h_le : (λ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t}) ≤ᵐ[ρ.fst] λ a, cond_kernel ρ a univ,
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
        rw lintegral_sub _ _ h_le,
        { exact kernel.measurable_prod_mk_mem _ ht, },
        { refine ((lintegral_mono_ae h_le).trans_lt _).ne,
          rw lintegral_cond_kernel_univ,
          exact measure_lt_top ρ univ, },
      end
    ... = ρ univ - ρ t : by rw [ht_eq, lintegral_cond_kernel_univ]
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
    calc ∫⁻ a, cond_kernel ρ a (⋃ i, {x | (a, x) ∈ f i}) ∂ρ.fst
        = ∫⁻ a, ∑' i, cond_kernel ρ a {x | (a, x) ∈ f i} ∂ρ.fst :
          by { congr' with a : 1, rw measure_Union (h_disj a) (h_meas a), }
    ... = ∑' i, ∫⁻ a, cond_kernel ρ a {x | (a, x) ∈ f i} ∂ρ.fst :
          begin
            rw lintegral_tsum (λ i : ℕ, measurable.ae_measurable _),
            exact kernel.measurable_prod_mk_mem _ (hf_meas i),
          end
    ... = ∑' i, ρ (f i) : by { congr' with i : 1, exact hf_eq i, }
    ... = ρ (Union f) : (measure_Union hf_disj hf_meas).symm, },
end

theorem disintegration' (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  (γ : Type*) [measurable_space γ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ) :=
begin
  ext a s hs : 2,
  rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  rw lintegral_cond_kernel ρ hs,
end

-- todo define someting to have a nicer expression?
theorem disintegration (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) (unit.star) :=
by rw [← disintegration' ρ unit, kernel.const_apply]

end probability_theory
