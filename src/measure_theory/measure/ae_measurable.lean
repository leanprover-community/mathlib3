/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.measure_space

/-!
# Almost everywhere measurable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `ae_measurable f μ`, is defined in the file `measure_space_def`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/

open measure_theory measure_theory.measure filter set function
open_locale measure_theory filter classical ennreal interval

variables {ι α β γ δ R : Type*} {m0 : measurable_space α} [measurable_space β]
   [measurable_space γ] [measurable_space δ] {f g : α → β} {μ ν : measure α}

include m0

section

@[nontriviality, measurability]
lemma subsingleton.ae_measurable [subsingleton α] : ae_measurable f μ :=
subsingleton.measurable.ae_measurable

@[nontriviality, measurability]
lemma ae_measurable_of_subsingleton_codomain [subsingleton β] : ae_measurable f μ :=
(measurable_of_subsingleton_codomain f).ae_measurable

@[simp, measurability] lemma ae_measurable_zero_measure : ae_measurable f (0 : measure α) :=
begin
  nontriviality α, inhabit α,
  exact ⟨λ x, f default, measurable_const, rfl⟩
end

namespace ae_measurable

lemma mono_measure (h : ae_measurable f μ) (h' : ν ≤ μ) : ae_measurable f ν :=
⟨h.mk f, h.measurable_mk, eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩

lemma mono_set {s t} (h : s ⊆ t) (ht : ae_measurable f (μ.restrict t)) :
  ae_measurable f (μ.restrict s) :=
ht.mono_measure (restrict_mono h le_rfl)

protected lemma mono' (h : ae_measurable f μ) (h' : ν ≪ μ) : ae_measurable f ν :=
⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

lemma ae_mem_imp_eq_mk {s} (h : ae_measurable f (μ.restrict s)) :
  ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
ae_imp_of_ae_restrict h.ae_eq_mk

lemma ae_inf_principal_eq_mk {s} (h : ae_measurable f (μ.restrict s)) :
  f =ᶠ[μ.ae ⊓ 𝓟 s] h.mk f :=
le_ae_restrict h.ae_eq_mk

@[measurability]
lemma sum_measure [countable ι] {μ : ι → measure α} (h : ∀ i, ae_measurable f (μ i)) :
  ae_measurable f (sum μ) :=
begin
  nontriviality β, inhabit β,
  set s : ι → set α := λ i, to_measurable (μ i) {x | f x ≠ (h i).mk f x},
  have hsμ : ∀ i, μ i (s i) = 0,
  { intro i, rw measure_to_measurable, exact (h i).ae_eq_mk },
  have hsm : measurable_set (⋂ i, s i),
    from measurable_set.Inter (λ i, measurable_set_to_measurable _ _),
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x,
  { intros i x hx, contrapose! hx, exact subset_to_measurable _ _ hx },
  set g : α → β := (⋂ i, s i).piecewise (const α default) f,
  refine ⟨g, measurable_of_restrict_of_restrict_compl hsm _ _, ae_sum_iff.mpr $ λ i, _⟩,
  { rw [restrict_piecewise], simp only [set.restrict, const], exact measurable_const },
  { rw [restrict_piecewise_compl, compl_Inter],
    intros t ht,
    refine ⟨⋃ i, ((h i).mk f ⁻¹' t) ∩ (s i)ᶜ, measurable_set.Union $
      λ i, (measurable_mk _ ht).inter (measurable_set_to_measurable _ _).compl, _⟩,
    ext ⟨x, hx⟩,
    simp only [mem_preimage, mem_Union, subtype.coe_mk, set.restrict, mem_inter_iff,
      mem_compl_iff] at hx ⊢,
    split,
    { rintro ⟨i, hxt, hxs⟩, rwa hs _ _ hxs },
    { rcases hx with ⟨i, hi⟩, rw hs _ _ hi, exact λ h, ⟨i, h, hi⟩ } },
  { refine measure_mono_null (λ x (hx : f x ≠ g x), _) (hsμ i),
    contrapose! hx, refine (piecewise_eq_of_not_mem _ _ _ _).symm,
    exact λ h, hx (mem_Inter.1 h i) }
end

@[simp] lemma _root_.ae_measurable_sum_measure_iff [countable ι] {μ : ι → measure α} :
  ae_measurable f (sum μ) ↔ ∀ i, ae_measurable f (μ i) :=
⟨λ h i, h.mono_measure (le_sum _ _), sum_measure⟩

@[simp] lemma _root_.ae_measurable_add_measure_iff :
  ae_measurable f (μ + ν) ↔ ae_measurable f μ ∧ ae_measurable f ν :=
by { rw [← sum_cond, ae_measurable_sum_measure_iff, bool.forall_bool, and.comm], refl }

@[measurability]
lemma add_measure {f : α → β} (hμ : ae_measurable f μ) (hν : ae_measurable f ν) :
  ae_measurable f (μ + ν) :=
ae_measurable_add_measure_iff.2 ⟨hμ, hν⟩

@[measurability]
protected lemma Union [countable ι] {s : ι → set α} (h : ∀ i, ae_measurable f (μ.restrict (s i))) :
  ae_measurable f (μ.restrict (⋃ i, s i)) :=
(sum_measure h).mono_measure $ restrict_Union_le

@[simp] lemma _root_.ae_measurable_Union_iff [countable ι] {s : ι → set α} :
  ae_measurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, ae_measurable f (μ.restrict (s i)) :=
⟨λ h i, h.mono_measure $ restrict_mono (subset_Union _ _) le_rfl, ae_measurable.Union⟩

@[simp] lemma _root_.ae_measurable_union_iff {s t : set α} :
  ae_measurable f (μ.restrict (s ∪ t)) ↔
    ae_measurable f (μ.restrict s) ∧ ae_measurable f (μ.restrict t) :=
by simp only [union_eq_Union, ae_measurable_Union_iff, bool.forall_bool, cond, and.comm]

@[measurability]
lemma smul_measure [monoid R] [distrib_mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
  (h : ae_measurable f μ) (c : R) :
  ae_measurable f (c • μ) :=
⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

lemma comp_ae_measurable {f : α → δ} {g : δ → β}
  (hg : ae_measurable g (μ.map f)) (hf : ae_measurable f μ) : ae_measurable (g ∘ f) μ :=
⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
  (ae_eq_comp hf hg.ae_eq_mk).trans ((hf.ae_eq_mk).fun_comp (mk g hg))⟩

lemma comp_measurable {f : α → δ} {g : δ → β}
  (hg : ae_measurable g (μ.map f)) (hf : measurable f) : ae_measurable (g ∘ f) μ :=
hg.comp_ae_measurable hf.ae_measurable

lemma comp_quasi_measure_preserving {ν : measure δ} {f : α → δ} {g : δ → β} (hg : ae_measurable g ν)
  (hf : quasi_measure_preserving f μ ν) : ae_measurable (g ∘ f) μ :=
(hg.mono' hf.absolutely_continuous).comp_measurable hf.measurable

lemma map_map_of_ae_measurable {g : β → γ} {f : α → β}
  (hg : ae_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  (μ.map f).map g = μ.map (g ∘ f) :=
begin
  ext1 s hs,
  let g' := hg.mk g,
  have A : map g (map f μ) = map g' (map f μ),
  { apply measure_theory.measure.map_congr,
    exact hg.ae_eq_mk },
  have B : map (g ∘ f) μ = map (g' ∘ f) μ,
  { apply measure_theory.measure.map_congr,
    exact ae_of_ae_map hf hg.ae_eq_mk },
  simp only [A, B, hs, hg.measurable_mk.ae_measurable.comp_ae_measurable hf, hg.measurable_mk,
    hg.measurable_mk hs, hf, map_apply, map_apply_of_ae_measurable],
  refl,
end

@[measurability]
lemma prod_mk {f : α → β} {g : α → γ} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, (f x, g x)) μ :=
⟨λ a, (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
  eventually_eq.prod_mk hf.ae_eq_mk hg.ae_eq_mk⟩

lemma exists_ae_eq_range_subset (H : ae_measurable f μ) {t : set β} (ht : ∀ᵐ x ∂μ, f x ∈ t)
  (h₀ : t.nonempty) :
  ∃ g, measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
begin
  let s : set α := to_measurable μ {x | f x = H.mk f x ∧ f x ∈ t}ᶜ,
  let g : α → β := piecewise s (λ x, h₀.some) (H.mk f),
  refine ⟨g, _, _, _⟩,
  { exact measurable.piecewise (measurable_set_to_measurable _ _)
      measurable_const H.measurable_mk },
  { rintros _ ⟨x, rfl⟩,
    by_cases hx : x ∈ s,
    { simpa [g, hx] using h₀.some_mem },
    { simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff],
      contrapose! hx,
      apply subset_to_measurable,
      simp only [hx, mem_compl_iff, mem_set_of_eq, not_and, not_false_iff, implies_true_iff]
        {contextual := tt} } },
  { have A : μ (to_measurable μ {x | f x = H.mk f x ∧ f x ∈ t}ᶜ) = 0,
    { rw [measure_to_measurable, ← compl_mem_ae_iff, compl_compl],
      exact H.ae_eq_mk.and ht },
    filter_upwards [compl_mem_ae_iff.2 A] with x hx,
    rw mem_compl_iff at hx,
    simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff],
    contrapose! hx,
    apply subset_to_measurable,
    simp only [hx, mem_compl_iff, mem_set_of_eq, false_and, not_false_iff] }
end

lemma exists_measurable_nonneg {β} [preorder β] [has_zero β] {mβ : measurable_space β} {f : α → β}
  (hf : ae_measurable f μ) (f_nn : ∀ᵐ t ∂μ, 0 ≤ f t) :
  ∃ g, measurable g ∧ 0 ≤ g ∧ f =ᵐ[μ] g :=
begin
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩,
  exact ⟨G, hG_meas, λ x, hG_mem (mem_range_self x), hG_ae_eq⟩,
end

lemma subtype_mk (h : ae_measurable f μ) {s : set β} {hfs : ∀ x, f x ∈ s} :
  ae_measurable (cod_restrict f s hfs) μ :=
begin
  nontriviality α, inhabit α,
  obtain ⟨g, g_meas, hg, fg⟩ : ∃ (g : α → β), measurable g ∧ range g ⊆ s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (eventually_of_forall hfs) ⟨_, hfs default⟩,
  refine ⟨cod_restrict g s (λ x, hg (mem_range_self _)), measurable.subtype_mk g_meas, _⟩,
  filter_upwards [fg] with x hx,
  simpa [subtype.ext_iff],
end

protected lemma null_measurable (h : ae_measurable f μ) : null_measurable f μ :=
let ⟨g, hgm, hg⟩ := h in hgm.null_measurable.congr hg.symm

end ae_measurable

lemma ae_measurable_const' (h : ∀ᵐ x y ∂μ, f x = f y) : ae_measurable f μ :=
begin
  rcases eq_or_ne μ 0 with rfl | hμ,
  { exact ae_measurable_zero_measure },
  { haveI := ae_ne_bot.2 hμ,
    rcases h.exists with ⟨x, hx⟩,
    exact ⟨const α (f x), measurable_const, eventually_eq.symm hx⟩ }
end

lemma ae_measurable_uIoc_iff [linear_order α] {f : α → β} {a b : α} :
  (ae_measurable f $ μ.restrict $ Ι a b) ↔
    (ae_measurable f $ μ.restrict $ Ioc a b) ∧ (ae_measurable f $ μ.restrict $ Ioc b a) :=
by rw [uIoc_eq_union, ae_measurable_union_iff]

lemma ae_measurable_iff_measurable [μ.is_complete] :
  ae_measurable f μ ↔ measurable f :=
⟨λ h, h.null_measurable.measurable_of_complete, λ h, h.ae_measurable⟩

lemma measurable_embedding.ae_measurable_map_iff {g : β → γ} (hf : measurable_embedding f) :
  ae_measurable g (μ.map f) ↔ ae_measurable (g ∘ f) μ :=
begin
  refine ⟨λ H, H.comp_measurable hf.measurable, _⟩,
  rintro ⟨g₁, hgm₁, heq⟩,
  rcases hf.exists_measurable_extend hgm₁ (λ x, ⟨g x⟩) with ⟨g₂, hgm₂, rfl⟩,
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
end

lemma measurable_embedding.ae_measurable_comp_iff {g : β → γ}
  (hg : measurable_embedding g) {μ : measure α} :
  ae_measurable (g ∘ f) μ ↔ ae_measurable f μ :=
begin
  refine ⟨λ H, _, hg.measurable.comp_ae_measurable⟩,
  suffices : ae_measurable ((range_splitting g ∘ range_factorization g) ∘ f) μ,
    by rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this,
  exact hg.measurable_range_splitting.comp_ae_measurable H.subtype_mk
end

lemma ae_measurable_restrict_iff_comap_subtype {s : set α} (hs : measurable_set s)
  {μ : measure α} {f : α → β} :
  ae_measurable f (μ.restrict s) ↔ ae_measurable (f ∘ coe : s → β) (comap coe μ) :=
by rw [← map_comap_subtype_coe hs, (measurable_embedding.subtype_coe hs).ae_measurable_map_iff]

@[simp, to_additive] lemma ae_measurable_one [has_one β] : ae_measurable (λ a : α, (1 : β)) μ :=
measurable_one.ae_measurable

@[simp] lemma ae_measurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
  ae_measurable f (c • μ) ↔ ae_measurable f μ :=
⟨λ h, ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).1 h.ae_eq_mk⟩,
  λ h, ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

lemma ae_measurable_of_ae_measurable_trim {α} {m m0 : measurable_space α}
  {μ : measure α} (hm : m ≤ m0) {f : α → β} (hf : ae_measurable f (μ.trim hm)) :
  ae_measurable f μ :=
⟨hf.mk f, measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

lemma ae_measurable_restrict_of_measurable_subtype {s : set α}
  (hs : measurable_set s) (hf : measurable (λ x : s, f x)) : ae_measurable f (μ.restrict s) :=
(ae_measurable_restrict_iff_comap_subtype hs).2 hf.ae_measurable

lemma ae_measurable_map_equiv_iff (e : α ≃ᵐ β) {f : β → γ} :
  ae_measurable f (μ.map e) ↔ ae_measurable (f ∘ e) μ :=
e.measurable_embedding.ae_measurable_map_iff

end

lemma ae_measurable.restrict (hfm : ae_measurable f μ) {s} :
  ae_measurable f (μ.restrict s) :=
⟨ae_measurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

lemma ae_measurable_Ioi_of_forall_Ioc {β} {mβ : measurable_space β}
  [linear_order α] [(at_top : filter α).is_countably_generated] {x : α} {g : α → β}
  (g_meas : ∀ t > x, ae_measurable g (μ.restrict (Ioc x t))) :
  ae_measurable g (μ.restrict (Ioi x)) :=
begin
  haveI : nonempty α := ⟨x⟩,
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (at_top : filter α),
  have Ioi_eq_Union : Ioi x = ⋃ n : ℕ, Ioc x (u n),
  { rw Union_Ioc_eq_Ioi_self_iff.mpr _,
    exact λ y _, (hu_tendsto.eventually (eventually_ge_at_top y)).exists },
  rw [Ioi_eq_Union, ae_measurable_Union_iff],
  intros n,
  cases lt_or_le x (u n),
  { exact g_meas (u n) h, },
  { rw [Ioc_eq_empty (not_lt.mpr h), measure.restrict_empty],
    exact ae_measurable_zero_measure, },
end

variables [has_zero β]

lemma ae_measurable_indicator_iff {s} (hs : measurable_set s) :
  ae_measurable (indicator s f) μ ↔ ae_measurable f (μ.restrict s) :=
begin
  split,
  { intro h,
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs) },
  { intro h,
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, _⟩,
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (ae_measurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans $ (indicator_ae_eq_restrict hs).symm),
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (ae_measurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm,
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B },
end

@[measurability]
lemma ae_measurable.indicator (hfm : ae_measurable f μ) {s} (hs : measurable_set s) :
  ae_measurable (s.indicator f) μ :=
(ae_measurable_indicator_iff hs).mpr hfm.restrict

lemma measure_theory.measure.restrict_map_of_ae_measurable
  {f : α → δ} (hf : ae_measurable f μ) {s : set δ} (hs : measurable_set s) :
  (μ.map f).restrict s = (μ.restrict $ f ⁻¹' s).map f :=
calc
(μ.map f).restrict s = (μ.map (hf.mk f)).restrict s :
  by { congr' 1, apply measure.map_congr hf.ae_eq_mk }
... = (μ.restrict $ (hf.mk f) ⁻¹' s).map (hf.mk f) :
  measure.restrict_map hf.measurable_mk hs
... = (μ.restrict $ (hf.mk f) ⁻¹' s).map f :
  measure.map_congr (ae_restrict_of_ae (hf.ae_eq_mk.symm))
... = (μ.restrict $ f ⁻¹' s).map f :
begin
  apply congr_arg,
  ext1 t ht,
  simp only [ht, measure.restrict_apply],
  apply measure_congr,
  apply (eventually_eq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)
end

lemma measure_theory.measure.map_mono_of_ae_measurable
  {f : α → δ} (h : μ ≤ ν) (hf : ae_measurable f ν) :
  μ.map f ≤ ν.map f :=
λ s hs, by simpa [hf, hs, hf.mono_measure h] using measure.le_iff'.1 h (f ⁻¹' s)
