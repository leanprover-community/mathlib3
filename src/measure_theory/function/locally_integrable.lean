/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.integrable_on

/-!
# Locally integrable functions

A function is called *locally integrable* (`measure_theory.locally_integrable`) if it is integrable
on a neighborhood of every point.

This file contains properties of locally integrable functions and integrability results
on compact sets.

## Main statements

* `continuous.locally_integrable`: A continuous function is locally integrable.

-/

open measure_theory measure_theory.measure set function topological_space
open_locale topology interval

variables {X Y E R : Type*} [measurable_space X] [topological_space X]
variables [measurable_space Y] [topological_space Y]
variables [normed_add_comm_group E] {f : X → E} {μ : measure X}

namespace measure_theory

/-- A function `f : X → E` is locally integrable if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `locally_integrable.integrable_on_is_compact`. -/
def locally_integrable (f : X → E) (μ : measure X . volume_tac) : Prop :=
∀ (x : X), integrable_at_filter f (𝓝 x) μ

lemma integrable.locally_integrable (hf : integrable f μ) : locally_integrable f μ :=
λ x, hf.integrable_at_filter _

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

/-- If a function is locally integrable, then it is integrable on any compact set. -/
lemma locally_integrable.integrable_on_is_compact {k : set X} (hf : locally_integrable f μ)
  (hk : is_compact k) : integrable_on f k μ :=
begin
  rcases hf.integrable_on_nhds_is_compact hk with ⟨u, u_open, ku, hu⟩,
  exact hu.mono_set ku
end

lemma locally_integrable_iff [locally_compact_space X] :
  locally_integrable f μ ↔ ∀ (k : set X), is_compact k → integrable_on f k μ :=
begin
  refine ⟨λ hf k hk, hf.integrable_on_is_compact hk, λ hf x, _⟩,
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x,
  exact ⟨K, h2K, hf K hK⟩,
end

lemma locally_integrable.ae_strongly_measurable [second_countable_topology X]
  (hf : locally_integrable f μ) : ae_strongly_measurable f μ :=
begin
  have : ∀ x, ∃ u, is_open u ∧ x ∈ u ∧ integrable_on f u μ,
  { assume x,
    rcases hf x with ⟨s, hs, h's⟩,
    rcases mem_nhds_iff.1 hs with ⟨u, us, u_open, xu⟩,
    exact ⟨u, u_open, xu, h's.mono_set us⟩ },
  choose u u_open xu hu using this,
  obtain ⟨T, T_count, hT⟩ : ∃ (T : set X), T.countable ∧ (⋃ (i : T), u i) = univ,
  { have : (⋃ x, u x) = univ, from eq_univ_of_forall (λ x, mem_Union_of_mem x (xu x)),
    rw ← this,
    simp only [Union_coe_set, subtype.coe_mk],
    exact is_open_Union_countable u u_open },
  haveI : countable T, from countable_coe_iff.mpr T_count,
  rw [← @restrict_univ _ _ μ, ← hT, ae_strongly_measurable_Union_iff],
  exact λ i, (hu i).ae_strongly_measurable,
end

lemma locally_integrable_const [is_locally_finite_measure μ] (c : E) :
  locally_integrable (λ x, c) μ :=
begin
  assume x,
  rcases μ.finite_at_nhds x with ⟨U, hU, h'U⟩,
  refine ⟨U, hU, _⟩,
  simp only [h'U, integrable_on_const, or_true],
end

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

section mul

variables [opens_measurable_space X] [normed_ring R] [second_countable_topology_either X R]
  {A K : set X} {g g' : X → R}

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

end measure_theory
open measure_theory

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
lemma is_compact.integrable_on_of_nhds_within {K : set X} (hK : is_compact K)
  (hf : ∀ x ∈ K, integrable_at_filter f (𝓝[K] x) μ) : integrable_on f K μ :=
is_compact.induction_on hK integrable_on_empty (λ s t hst ht, ht.mono_set hst)
  (λ s t hs ht, hs.union ht) hf

section borel

variables [opens_measurable_space X] [is_locally_finite_measure μ]
variables {K : set X} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
lemma continuous.locally_integrable [second_countable_topology_either X E]
  (hf : continuous f) : locally_integrable f μ :=
hf.integrable_at_nhds

variables [metrizable_space X]

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
lemma continuous_on.integrable_on_compact (hK : is_compact K) (hf : continuous_on f K) :
  integrable_on f K μ :=
begin
  letI := metrizable_space_metric X,
  apply hK.integrable_on_of_nhds_within (λ x hx, _),
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
  {s : set X}

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
