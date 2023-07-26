/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.integrable_on

/-!
# Locally integrable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function is called *locally integrable* (`measure_theory.locally_integrable`) if it is integrable
on a neighborhood of every point. More generally, it is *locally integrable on `s`* if it is
locally integrable on a neighbourhood within `s` of any point of `s`.

This file contains properties of locally integrable functions, and integrability results
on compact sets.

## Main statements

* `continuous.locally_integrable`: A continuous function is locally integrable.
* `continuous_on.locally_integrable_on`: A function which is continuous on `s` is locally
  integrable on `s`.
-/

open measure_theory measure_theory.measure set function topological_space
open_locale topology interval

variables {X Y E R : Type*} [measurable_space X] [topological_space X]
variables [measurable_space Y] [topological_space Y]
variables [normed_add_comm_group E] {f : X → E} {μ : measure X} {s : set X}

namespace measure_theory

section locally_integrable_on

/-- A function `f : X → E` is *locally integrable on s*, for `s ⊆ X`, if for every `x ∈ s` there is
a neighbourhood of `x` within `s` on which `f` is integrable. (Note this is, in general, strictly
weaker than local integrability with respect to `μ.restrict s`.) -/
def locally_integrable_on (f : X → E) (s : set X) (μ : measure X . volume_tac) : Prop :=
∀ (x : X), x ∈ s → integrable_at_filter f (𝓝[s] x) μ

lemma locally_integrable_on.mono
  (hf : measure_theory.locally_integrable_on f s μ) {t : set X} (hst : t ⊆ s) :
  locally_integrable_on f t μ :=
λ x hx, (hf x $ hst hx).filter_mono (nhds_within_mono x hst)

lemma locally_integrable_on.norm (hf : locally_integrable_on f s μ) :
  locally_integrable_on (λ x, ‖f x‖) s μ :=
λ t ht, let ⟨U, hU_nhd, hU_int⟩ := hf t ht in ⟨U, hU_nhd, hU_int.norm⟩

lemma integrable_on.locally_integrable_on (hf : integrable_on f s μ) :
  locally_integrable_on f s μ :=
λ x hx, ⟨s, self_mem_nhds_within, hf⟩

/-- If a function is locally integrable on a compact set, then it is integrable on that set. -/
lemma locally_integrable_on.integrable_on_is_compact
  (hf : locally_integrable_on f s μ) (hs : is_compact s) :
  integrable_on f s μ :=
is_compact.induction_on hs integrable_on_empty (λ u v huv hv, hv.mono_set huv)
  (λ u v hu hv, integrable_on_union.mpr ⟨hu, hv⟩) hf

lemma locally_integrable_on.integrable_on_compact_subset
  (hf : locally_integrable_on f s μ) {t : set X} (hst : t ⊆ s) (ht : is_compact t) :
  integrable_on f t μ :=
(hf.mono hst).integrable_on_is_compact ht

lemma locally_integrable_on.ae_strongly_measurable [second_countable_topology X]
  (hf : locally_integrable_on f s μ) :
  ae_strongly_measurable f (μ.restrict s) :=
begin
  have : ∀ (x : s), ∃ u, is_open u ∧ x.1 ∈ u ∧ integrable_on f (u ∩ s) μ,
  { rintro ⟨x, hx⟩,
    rcases hf x hx with ⟨t, ht, h't⟩,
    rcases mem_nhds_within.1 ht with ⟨u, u_open, x_mem, u_sub⟩,
    refine ⟨u, u_open, x_mem, h't.mono_set u_sub⟩ },
  choose u u_open xu hu using this,
  obtain ⟨T, T_count, hT⟩ : ∃ (T : set s), T.countable ∧ s = (⋃ (i : T), u i ∩ s),
  { have : s ⊆ (⋃ (x : s), u x), from λ y hy, mem_Union_of_mem ⟨y, hy⟩ (xu ⟨y, hy⟩),
    obtain ⟨T, hT_count, hT_un⟩ := is_open_Union_countable u u_open,
    refine ⟨T, hT_count, _⟩,
    rw [←hT_un, bUnion_eq_Union] at this,
    rw [←Union_inter, eq_comm, inter_eq_right_iff_subset],
    exact this },
  haveI : countable T, from countable_coe_iff.mpr T_count,
  rw [hT, ae_strongly_measurable_Union_iff],
  exact λ (i : T), (hu i).ae_strongly_measurable,
end

/-- If `s` is either open, or closed, then `f` is locally integrable on `s` iff it is integrable on
every compact subset contained in `s`. -/
lemma locally_integrable_on_iff [locally_compact_space X] [t2_space X]
  (hs : is_closed s ∨ is_open s) :
  locally_integrable_on f s μ ↔ ∀ (k : set X) (hk : k ⊆ s), is_compact k → integrable_on f k μ :=
begin
  -- The correct condition is that `s` be *locally closed*, i.e. for every `x ∈ s` there is some
  -- `U ∈ 𝓝 x` such that `U ∩ s` is closed. But mathlib doesn't have locally closed sets yet.
  refine ⟨λ hf k hk, hf.integrable_on_compact_subset hk, λ hf x hx, _⟩,
  cases hs,
  { exact let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x in ⟨_, inter_mem_nhds_within s h2K,
    hf _ (inter_subset_left _ _) (is_compact_of_is_closed_subset hK (hs.inter hK.is_closed)
    (inter_subset_right _ _))⟩ },
  { obtain ⟨K, hK, h2K, h3K⟩ := exists_compact_subset hs hx,
    refine ⟨K, _, hf K h3K hK⟩,
    simpa only [is_open.nhds_within_eq hs hx, interior_eq_nhds'] using h2K }
end

end locally_integrable_on

/-- A function `f : X → E` is *locally integrable* if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `locally_integrable.integrable_on_is_compact`. -/
def locally_integrable (f : X → E) (μ : measure X . volume_tac) : Prop :=
∀ (x : X), integrable_at_filter f (𝓝 x) μ

lemma locally_integrable_on_univ : locally_integrable_on f univ μ ↔ locally_integrable f μ :=
by simpa only [locally_integrable_on, nhds_within_univ, mem_univ, true_implies_iff]

lemma locally_integrable.locally_integrable_on (hf : locally_integrable f μ) (s : set X) :
  locally_integrable_on f s μ :=
λ x hx, (hf x).filter_mono nhds_within_le_nhds

lemma integrable.locally_integrable (hf : integrable f μ) : locally_integrable f μ :=
λ x, hf.integrable_at_filter _

/-- If `f` is locally integrable with respect to `μ.restrict s`, it is locally integrable on `s`.
(See `locally_integrable_on_iff_locally_integrable_restrict` for an iff statement when `s` is
closed.) -/
lemma locally_integrable_on_of_locally_integrable_restrict [opens_measurable_space X]
  (hf : locally_integrable f (μ.restrict s)) :
  locally_integrable_on f s μ :=
begin
  intros x hx,
  obtain ⟨t, ht_mem, ht_int⟩ := hf x,
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem,
  refine ⟨_, inter_mem_nhds_within s (hu_o.mem_nhds hu_mem), _⟩,
  simpa only [integrable_on, measure.restrict_restrict hu_o.measurable_set, inter_comm]
    using ht_int.mono_set hu_sub,
end

/-- If `s` is closed, being locally integrable on `s` wrt `μ` is equivalent to being locally
integrable with respect to `μ.restrict s`. For the one-way implication without assuming `s` closed,
see `locally_integrable_on_of_locally_integrable_restrict`. -/
lemma locally_integrable_on_iff_locally_integrable_restrict [opens_measurable_space X]
  (hs : is_closed s) :
  locally_integrable_on f s μ ↔ locally_integrable f (μ.restrict s) :=
begin
  refine ⟨λ hf x, _, locally_integrable_on_of_locally_integrable_restrict⟩,
  by_cases h : x ∈ s,
  { obtain ⟨t, ht_nhds, ht_int⟩ := hf x h,
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhds_within.mp ht_nhds,
    refine ⟨u, hu_o.mem_nhds hu_x, _⟩,
    rw [integrable_on, restrict_restrict hu_o.measurable_set],
    exact ht_int.mono_set hu_sub },
  { rw ←is_open_compl_iff at hs,
    refine ⟨sᶜ, hs.mem_nhds h, _⟩,
    rw [integrable_on, restrict_restrict, inter_comm, inter_compl_self, ←integrable_on],
    exacts [integrable_on_empty, hs.measurable_set] },
end

/-- If a function is locally integrable, then it is integrable on any compact set. -/
lemma locally_integrable.integrable_on_is_compact {k : set X} (hf : locally_integrable f μ)
  (hk : is_compact k) : integrable_on f k μ :=
(hf.locally_integrable_on k).integrable_on_is_compact hk

/-- If a function is locally integrable, then it is integrable on an open neighborhood of any
compact set. -/
lemma locally_integrable.integrable_on_nhds_is_compact (hf : locally_integrable f μ) {k : set X}
  (hk : is_compact k) : ∃ u, is_open u ∧ k ⊆ u ∧ integrable_on f u μ :=
begin
  refine is_compact.induction_on hk _ _ _ _,
  { refine ⟨∅, is_open_empty, subset.rfl, integrable_on_empty⟩ },
  { rintros s t hst ⟨u, u_open, tu, hu⟩,
    exact ⟨u, u_open, hst.trans tu, hu⟩ },
  { rintros s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩,
    exact ⟨u ∪ v, u_open.union v_open, union_subset_union su tv, hu.union hv⟩ },
  { assume x hx,
    rcases hf x with ⟨u, ux, hu⟩,
    rcases mem_nhds_iff.1 ux with ⟨v, vu, v_open, xv⟩,
    exact ⟨v, nhds_within_le_nhds (v_open.mem_nhds xv), v, v_open, subset.rfl, hu.mono_set vu⟩ }
end

lemma locally_integrable_iff [locally_compact_space X] :
  locally_integrable f μ ↔ ∀ (k : set X), is_compact k → integrable_on f k μ :=
⟨λ hf k hk, hf.integrable_on_is_compact hk,
  λ hf x, let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x in ⟨K, h2K, hf K hK⟩⟩

lemma locally_integrable.ae_strongly_measurable [second_countable_topology X]
  (hf : locally_integrable f μ) : ae_strongly_measurable f μ :=
by simpa only [restrict_univ] using (locally_integrable_on_univ.mpr hf).ae_strongly_measurable

lemma locally_integrable_const [is_locally_finite_measure μ] (c : E) :
  locally_integrable (λ x, c) μ :=
begin
  assume x,
  rcases μ.finite_at_nhds x with ⟨U, hU, h'U⟩,
  refine ⟨U, hU, _⟩,
  simp only [h'U, integrable_on_const, or_true],
end

lemma locally_integrable_on_const [is_locally_finite_measure μ] (c : E) :
  locally_integrable_on (λ x, c) s μ :=
(locally_integrable_const c).locally_integrable_on s

lemma locally_integrable.indicator (hf : locally_integrable f μ)
  {s : set X} (hs : measurable_set s) : locally_integrable (s.indicator f) μ :=
begin
  assume x,
  rcases hf x with ⟨U, hU, h'U⟩,
  exact ⟨U, hU, h'U.indicator hs⟩,
end

theorem locally_integrable_map_homeomorph [borel_space X] [borel_space Y]
  (e : X ≃ₜ Y) {f : Y → E} {μ : measure X} :
  locally_integrable f (measure.map e μ) ↔ locally_integrable (f ∘ e) μ :=
begin
  refine ⟨λ h x, _, λ h x, _⟩,
  { rcases h (e x) with ⟨U, hU, h'U⟩,
    refine ⟨e ⁻¹' U, e.continuous.continuous_at.preimage_mem_nhds hU, _⟩,
    exact (integrable_on_map_equiv e.to_measurable_equiv).1 h'U },
  { rcases h (e.symm x) with ⟨U, hU, h'U⟩,
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.continuous_at.preimage_mem_nhds hU, _⟩,
    apply (integrable_on_map_equiv e.to_measurable_equiv).2,
    simp only [homeomorph.to_measurable_equiv_coe],
    convert h'U,
    ext x,
    simp only [mem_preimage, homeomorph.symm_apply_apply] }
end

end measure_theory

open measure_theory

section borel

variables [opens_measurable_space X] [is_locally_finite_measure μ]
variables {K : set X} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
lemma continuous.locally_integrable [second_countable_topology_either X E]
  (hf : continuous f) : locally_integrable f μ :=
hf.integrable_at_nhds

/-- A function `f` continuous on a set `K` is locally integrable on this set with respect
to any locally finite measure. -/
lemma continuous_on.locally_integrable_on [second_countable_topology_either X E]
  (hf : continuous_on f K) (hK : measurable_set K) :
  locally_integrable_on f K μ :=
λ x hx, hf.integrable_at_nhds_within hK hx

variables [metrizable_space X]

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
lemma continuous_on.integrable_on_compact (hK : is_compact K) (hf : continuous_on f K) :
  integrable_on f K μ :=
begin
  letI := metrizable_space_metric X,
  refine locally_integrable_on.integrable_on_is_compact (λ x hx, _) hK,
  exact hf.integrable_at_nhds_within_of_is_separable hK.measurable_set hK.is_separable hx,
end

lemma continuous_on.integrable_on_Icc [preorder X] [compact_Icc_space X]
  (hf : continuous_on f (Icc a b)) : integrable_on f (Icc a b) μ :=
hf.integrable_on_compact is_compact_Icc

lemma continuous.integrable_on_Icc [preorder X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f (Icc a b) μ :=
hf.continuous_on.integrable_on_Icc

lemma continuous.integrable_on_Ioc [preorder X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f (Ioc a b) μ :=
hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self

lemma continuous_on.integrable_on_uIcc [linear_order X] [compact_Icc_space X]
  (hf : continuous_on f [a, b]) : integrable_on f [a, b] μ :=
hf.integrable_on_Icc

lemma continuous.integrable_on_uIcc [linear_order X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f [a, b] μ :=
hf.integrable_on_Icc

lemma continuous.integrable_on_uIoc [linear_order X] [compact_Icc_space X]
  (hf : continuous f) : integrable_on f (Ι a b) μ :=
hf.integrable_on_Ioc

/-- A continuous function with compact support is integrable on the whole space. -/
lemma continuous.integrable_of_has_compact_support
  (hf : continuous f) (hcf : has_compact_support f) : integrable f μ :=
(integrable_on_iff_integrable_of_support_subset (subset_tsupport f)).mp $
  hf.continuous_on.integrable_on_compact hcf

end borel

open_locale ennreal

section monotone

variables [borel_space X]
  [conditionally_complete_linear_order X] [conditionally_complete_linear_order E]
  [order_topology X] [order_topology E] [second_countable_topology E]

lemma monotone_on.integrable_on_of_measure_ne_top
  (hmono : monotone_on f s) {a b : X} (ha : is_least s a) (hb : is_greatest s b) (hs : μ s ≠ ∞)
  (h's : measurable_set s) :
  integrable_on f s μ :=
begin
  borelize E,
  obtain rfl | h := s.eq_empty_or_nonempty,
  { exact integrable_on_empty },
  have hbelow : bdd_below (f '' s) := ⟨f a, λ x ⟨y, hy, hyx⟩, hyx ▸ hmono ha.1 hy (ha.2 hy)⟩,
  have habove : bdd_above (f '' s) := ⟨f b, λ x ⟨y, hy, hyx⟩, hyx ▸ hmono hy hb.1 (hb.2 hy)⟩,
  have : metric.bounded (f '' s) := metric.bounded_of_bdd_above_of_bdd_below habove hbelow,
  rcases bounded_iff_forall_norm_le.mp this with ⟨C, hC⟩,
  have A : integrable_on (λ x, C) s μ, by simp only [hs.lt_top, integrable_on_const, or_true],
  refine integrable.mono' A
    (ae_measurable_restrict_of_monotone_on h's hmono).ae_strongly_measurable
    ((ae_restrict_iff' h's).mpr $ ae_of_all _ $
      λ y hy, hC (f y) (mem_image_of_mem f hy)),
end

lemma monotone_on.integrable_on_is_compact [is_finite_measure_on_compacts μ]
  (hs : is_compact s) (hmono : monotone_on f s) :
  integrable_on f s μ :=
begin
  obtain rfl | h := s.eq_empty_or_nonempty,
  { exact integrable_on_empty },
  { exact hmono.integrable_on_of_measure_ne_top (hs.is_least_Inf h) (hs.is_greatest_Sup h)
    hs.measure_lt_top.ne hs.measurable_set }
end

lemma antitone_on.integrable_on_of_measure_ne_top
  (hanti : antitone_on f s) {a b : X} (ha : is_least s a) (hb : is_greatest s b) (hs : μ s ≠ ∞)
  (h's : measurable_set s) :
  integrable_on f s μ :=
hanti.dual_right.integrable_on_of_measure_ne_top ha hb  hs h's

lemma antione_on.integrable_on_is_compact [is_finite_measure_on_compacts μ]
  (hs : is_compact s) (hanti : antitone_on f s) :
  integrable_on f s μ :=
hanti.dual_right.integrable_on_is_compact hs

lemma monotone.locally_integrable [is_locally_finite_measure μ] (hmono : monotone f) :
  locally_integrable f μ :=
begin
  assume x,
  rcases μ.finite_at_nhds x with ⟨U, hU, h'U⟩,
  obtain ⟨a, b, xab, hab, abU⟩ : ∃ (a b : X), x ∈ Icc a b ∧ Icc a b ∈ 𝓝 x ∧ Icc a b ⊆ U,
    from exists_Icc_mem_subset_of_mem_nhds hU,
  have ab : a ≤ b := xab.1.trans xab.2,
  refine ⟨Icc a b, hab, _⟩,
  exact (hmono.monotone_on _).integrable_on_of_measure_ne_top (is_least_Icc ab)
    (is_greatest_Icc ab) ((measure_mono abU).trans_lt h'U).ne measurable_set_Icc,
end

lemma antitone.locally_integrable [is_locally_finite_measure μ] (hanti : antitone f) :
  locally_integrable f μ :=
hanti.dual_right.locally_integrable

end monotone

namespace measure_theory

variables [opens_measurable_space X] {A K : set X}

section mul

variables [normed_ring R] [second_countable_topology_either X R] {g g' : X → R}

lemma integrable_on.mul_continuous_on_of_subset
  (hg : integrable_on g A μ) (hg' : continuous_on g' K)
  (hA : measurable_set A) (hK : is_compact K) (hAK : A ⊆ K) :
  integrable_on (λ x, g x * g' x) A μ :=
begin
  rcases is_compact.exists_bound_of_continuous_on hK hg' with ⟨C, hC⟩,
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg ⊢,
  have : ∀ᵐ x ∂(μ.restrict A), ‖g x * g' x‖ ≤ C * ‖g x‖,
  { filter_upwards [ae_restrict_mem hA] with x hx,
    refine (norm_mul_le _ _).trans _,
    rw mul_comm,
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (norm_nonneg _), },
  exact mem_ℒp.of_le_mul hg (hg.ae_strongly_measurable.mul $
    (hg'.mono hAK).ae_strongly_measurable hA) this,
end

lemma integrable_on.mul_continuous_on [t2_space X]
  (hg : integrable_on g K μ) (hg' : continuous_on g' K) (hK : is_compact K) :
  integrable_on (λ x, g x * g' x) K μ :=
hg.mul_continuous_on_of_subset hg' hK.measurable_set hK (subset.refl _)

lemma integrable_on.continuous_on_mul_of_subset
  (hg : continuous_on g K) (hg' : integrable_on g' A μ)
  (hK : is_compact K) (hA : measurable_set A) (hAK : A ⊆ K) :
  integrable_on (λ x, g x * g' x) A μ :=
begin
  rcases is_compact.exists_bound_of_continuous_on hK hg with ⟨C, hC⟩,
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg' ⊢,
  have : ∀ᵐ x ∂(μ.restrict A), ‖g x * g' x‖ ≤ C * ‖g' x‖,
  { filter_upwards [ae_restrict_mem hA] with x hx,
    refine (norm_mul_le _ _).trans _,
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (norm_nonneg _), },
  exact mem_ℒp.of_le_mul hg' (((hg.mono hAK).ae_strongly_measurable hA).mul
    hg'.ae_strongly_measurable) this,
end

lemma integrable_on.continuous_on_mul [t2_space X]
  (hg : continuous_on g K) (hg' : integrable_on g' K μ) (hK : is_compact K) :
  integrable_on (λ x, g x * g' x) K μ :=
hg'.continuous_on_mul_of_subset hg hK hK.measurable_set subset.rfl

end mul

section smul

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma integrable_on.continuous_on_smul [t2_space X] [second_countable_topology_either X 𝕜]
  {g : X → E} (hg : integrable_on g K μ) {f : X → 𝕜} (hf : continuous_on f K) (hK : is_compact K) :
  integrable_on (λ x, f x • g x) K μ :=
begin
  rw [integrable_on, ←integrable_norm_iff],
  { simp_rw norm_smul,
    refine integrable_on.continuous_on_mul _ hg.norm hK,
    exact continuous_norm.comp_continuous_on hf },
  { exact (hf.ae_strongly_measurable hK.measurable_set).smul hg.1 }
end

lemma integrable_on.smul_continuous_on [t2_space X] [second_countable_topology_either X E]
  {f : X → 𝕜} (hf : integrable_on f K μ) {g : X → E} (hg : continuous_on g K) (hK : is_compact K) :
  integrable_on (λ x, f x • g x) K μ :=
begin
  rw [integrable_on, ←integrable_norm_iff],
  { simp_rw norm_smul,
    refine integrable_on.mul_continuous_on hf.norm _ hK,
    exact continuous_norm.comp_continuous_on hg },
  { exact hf.1.smul (hg.ae_strongly_measurable hK.measurable_set) }
end

end smul

namespace locally_integrable_on

lemma continuous_on_mul [locally_compact_space X] [t2_space X] [normed_ring R]
  [second_countable_topology_either X R]
  {f g : X → R} {s : set X}
  (hf : locally_integrable_on f s μ) (hg : continuous_on g s) (hs : is_open s) :
  locally_integrable_on (λ x, g x * f x) s μ :=
begin
  rw measure_theory.locally_integrable_on_iff (or.inr hs) at hf ⊢,
  exact λ k hk_sub hk_c, (hf k hk_sub hk_c).continuous_on_mul (hg.mono hk_sub) hk_c
end

lemma mul_continuous_on [locally_compact_space X] [t2_space X] [normed_ring R]
  [second_countable_topology_either X R] {f g : X → R} {s : set X}
  (hf : locally_integrable_on f s μ) (hg : continuous_on g s) (hs : is_open s) :
  locally_integrable_on (λ x, f x * g x) s μ :=
begin
  rw measure_theory.locally_integrable_on_iff (or.inr hs) at hf ⊢,
  exact λ k hk_sub hk_c, (hf k hk_sub hk_c).mul_continuous_on (hg.mono hk_sub) hk_c
end

lemma continuous_on_smul [locally_compact_space X] [t2_space X]
  {𝕜 : Type*} [normed_field 𝕜] [second_countable_topology_either X 𝕜] [normed_space 𝕜 E]
  {f : X → E} {g : X → 𝕜} {s : set X} (hs : is_open s)
  (hf : locally_integrable_on f s μ) (hg : continuous_on g s) :
  locally_integrable_on (λ x, g x • f x) s μ :=
begin
  rw measure_theory.locally_integrable_on_iff (or.inr hs) at hf ⊢,
  exact λ k hk_sub hk_c, (hf k hk_sub hk_c).continuous_on_smul (hg.mono hk_sub) hk_c
end

lemma smul_continuous_on [locally_compact_space X] [t2_space X]
  {𝕜 : Type*} [normed_field 𝕜] [second_countable_topology_either X E] [normed_space 𝕜 E]
  {f : X → 𝕜} {g : X → E} {s : set X} (hs : is_open s)
  (hf : locally_integrable_on f s μ) (hg : continuous_on g s)  :
  locally_integrable_on (λ x, f x • g x) s μ :=
begin
  rw measure_theory.locally_integrable_on_iff (or.inr hs) at hf ⊢,
  exact λ k hk_sub hk_c, (hf k hk_sub hk_c).smul_continuous_on (hg.mono hk_sub) hk_c
end

end locally_integrable_on

end measure_theory
