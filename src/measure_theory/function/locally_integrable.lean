/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.integrable_on

/-!
# Locally integrable functions

A function is called *locally integrable* (`measure_theory.locally_integrable`) if it is integrable
on every compact subset of its domain.

This file contains properties of locally integrable functions and of integrability results
on compact sets.

## Main statements

* `continuous.locally_integrable`: A continuous function is locally integrable.

-/

open measure_theory measure_theory.measure set function topological_space
open_locale topological_space interval

variables {X Y E : Type*} [measurable_space X] [topological_space X]
variables [measurable_space Y] [topological_space Y]
variables [normed_group E] [measurable_space E] {f : X → E} {μ : measure X}

namespace measure_theory

/-- A function `f : X → E` is locally integrable if it is integrable on all compact sets.
  See `measure_theory.locally_integrable_iff` for the justification of this name. -/
def locally_integrable (f : X → E) (μ : measure X . volume_tac) : Prop :=
∀ ⦃K⦄, is_compact K → integrable_on f K μ

lemma integrable.locally_integrable (hf : integrable f μ) : locally_integrable f μ :=
λ K hK, hf.integrable_on

lemma locally_integrable.ae_measurable [sigma_compact_space X] (hf : locally_integrable f μ) :
  ae_measurable f μ :=
begin
  rw [← @restrict_univ _ _ μ, ← Union_compact_covering, ae_measurable_Union_iff],
  exact λ i, (hf $ is_compact_compact_covering X i).ae_measurable
end

lemma locally_integrable_iff [locally_compact_space X] :
  locally_integrable f μ ↔ ∀ x : X, ∃ U ∈ 𝓝 x, integrable_on f U μ :=
begin
  refine ⟨λ hf x, _, λ hf K hK, _⟩,
  { obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x, exact ⟨K, h2K, hf hK⟩ },
  { refine is_compact.induction_on hK integrable_on_empty (λ s t hst h, h.mono_set hst)
      (λ s t hs ht, integrable_on_union.mpr ⟨hs, ht⟩) (λ x hx, _),
    obtain ⟨K, hK, h2K⟩ := hf x,
    exact ⟨K, nhds_within_le_nhds hK, h2K⟩ }
end

section real
variables [opens_measurable_space X] {A K : set X} {g g' : X → ℝ}

lemma integrable_on.mul_continuous_on_of_subset
  (hg : integrable_on g A μ) (hg' : continuous_on g' K)
  (hA : measurable_set A) (hK : is_compact K) (hAK : A ⊆ K) :
  integrable_on (λ x, g x * g' x) A μ :=
begin
  rcases is_compact.exists_bound_of_continuous_on hK hg' with ⟨C, hC⟩,
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg ⊢,
  have : ∀ᵐ x ∂(μ.restrict A), ∥g x * g' x∥ ≤ C * ∥g x∥,
  { filter_upwards [ae_restrict_mem hA] with x hx,
    rw [real.norm_eq_abs, abs_mul, mul_comm, real.norm_eq_abs],
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (abs_nonneg _), },
  exact mem_ℒp.of_le_mul hg (hg.ae_measurable.mul ((hg'.mono hAK).ae_measurable hA)) this,
end

lemma integrable_on.mul_continuous_on [t2_space X]
  (hg : integrable_on g K μ) (hg' : continuous_on g' K) (hK : is_compact K) :
  integrable_on (λ x, g x * g' x) K μ :=
hg.mul_continuous_on_of_subset hg' hK.measurable_set hK (subset.refl _)

lemma integrable_on.continuous_on_mul_of_subset
  (hg : continuous_on g K) (hg' : integrable_on g' A μ)
  (hK : is_compact K) (hA : measurable_set A) (hAK : A ⊆ K) :
  integrable_on (λ x, g x * g' x) A μ :=
by simpa [mul_comm] using hg'.mul_continuous_on_of_subset hg hA hK hAK

lemma integrable_on.continuous_on_mul [t2_space X]
  (hg : continuous_on g K) (hg' : integrable_on g' K μ) (hK : is_compact K) :
  integrable_on (λ x, g x * g' x) K μ :=
integrable_on.continuous_on_mul_of_subset hg hg' hK hK.measurable_set subset.rfl

end real

end measure_theory
open measure_theory

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
lemma is_compact.integrable_on_of_nhds_within {K : set X} (hK : is_compact K)
  (hf : ∀ x ∈ K, integrable_at_filter f (𝓝[K] x) μ) : integrable_on f K μ :=
is_compact.induction_on hK integrable_on_empty (λ s t hst ht, ht.mono_set hst)
  (λ s t hs ht, hs.union ht) hf

section borel

variables [opens_measurable_space X] [t2_space X] [borel_space E] [is_locally_finite_measure μ]
variables {K : set X} {a b : X}

/-- A function `f` continuous on a compact set `s` is integrable on this set with respect to any
locally finite measure. -/
lemma continuous_on.integrable_on_compact (hK : is_compact K) (hf : continuous_on f K) :
  integrable_on f K μ :=
hK.integrable_on_of_nhds_within $ λ x hx, hf.integrable_at_nhds_within hK.measurable_set hx

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
lemma continuous.locally_integrable (hf : continuous f) : locally_integrable f μ :=
λ s hs, hf.continuous_on.integrable_on_compact hs

lemma continuous_on.integrable_on_Icc [preorder X] [compact_Icc_space X]
  (hf : continuous_on f (Icc a b)) : integrable_on f (Icc a b) μ :=
hf.integrable_on_compact is_compact_Icc

lemma continuous.integrable_on_Icc [preorder X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f (Icc a b) μ :=
hf.locally_integrable is_compact_Icc

lemma continuous.integrable_on_Ioc [preorder X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f (Ioc a b) μ :=
hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self

lemma continuous_on.integrable_on_interval [linear_order X] [compact_Icc_space X]
  (hf : continuous_on f [a, b]) : integrable_on f [a, b] μ :=
hf.integrable_on_Icc

lemma continuous.integrable_on_interval [linear_order X] [compact_Icc_space X] (hf : continuous f) :
  integrable_on f [a, b] μ :=
hf.integrable_on_Icc

lemma continuous.integrable_on_interval_oc [linear_order X] [compact_Icc_space X]
  (hf : continuous f) : integrable_on f (Ι a b) μ :=
hf.integrable_on_Ioc

/-- A continuous function with compact support is integrable on the whole space. -/
lemma continuous.integrable_of_has_compact_support
  (hf : continuous f) (hcf : has_compact_support f) : integrable f μ :=
(integrable_on_iff_integable_of_support_subset (subset_tsupport f) measurable_set_closure).mp $
  hf.locally_integrable hcf

end borel

section monotone

variables [borel_space X] [borel_space E]
  [conditionally_complete_linear_order X] [conditionally_complete_linear_order E]
  [order_topology X] [order_topology E] [second_countable_topology E]
  [is_locally_finite_measure μ] {s : set X}

lemma monotone_on.integrable_on_compact (hs : is_compact s) (hmono : monotone_on f s) :
  integrable_on f s μ :=
begin
  obtain rfl | h := s.eq_empty_or_nonempty,
  { exact integrable_on_empty },
  have hbelow : bdd_below (f '' s) :=
    ⟨f (Inf s), λ x ⟨y, hy, hyx⟩, hyx ▸ hmono (hs.Inf_mem h) hy (cInf_le hs.bdd_below hy)⟩,
  have habove : bdd_above (f '' s) :=
    ⟨f (Sup s), λ x ⟨y, hy, hyx⟩, hyx ▸ hmono hy (hs.Sup_mem h) (le_cSup hs.bdd_above hy)⟩,
  have : metric.bounded (f '' s) := metric.bounded_of_bdd_above_of_bdd_below habove hbelow,
  rcases bounded_iff_forall_norm_le.mp this with ⟨C, hC⟩,
  exact integrable.mono' (continuous_const.locally_integrable hs)
    (ae_measurable_restrict_of_monotone_on hs.measurable_set hmono)
    ((ae_restrict_iff' hs.measurable_set).mpr $ ae_of_all _ $
      λ y hy, hC (f y) (mem_image_of_mem f hy)),
end

lemma antitone_on.integrable_on_compact (hs : is_compact s) (hanti : antitone_on f s) :
  integrable_on f s μ :=
@monotone_on.integrable_on_compact X (order_dual E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs hanti

lemma monotone.locally_integrable (hmono : monotone f) : locally_integrable f μ :=
λ s hs, monotone_on.integrable_on_compact hs (λ x y _ _ hxy, hmono hxy)

lemma antitone.locally_integrable (hanti : antitone f) : locally_integrable f μ :=
@monotone.locally_integrable X (order_dual E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hanti

end monotone
