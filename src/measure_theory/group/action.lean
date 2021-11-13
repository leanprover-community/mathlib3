/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.measurable_equiv
import dynamics.ergodic.measure_preserving

/-!
-/

open_locale ennreal pointwise
open measure_theory measure_theory.measure set function

namespace measure_theory

variables {G M α : Type*} [measurable_space α]

class vadd_invariant_measure (M α : Type*) [has_vadd M α] [measurable_space α]
  (μ : set α → ℝ≥0∞) : Prop :=
(measure_preimage_vadd [] : ∀ (c : M) ⦃s : set α⦄, measurable_set s → μ ((λ x, c +ᵥ x) ⁻¹' s) = μ s)

@[to_additive] class smul_invariant_measure (M α : Type*) [has_scalar M α] [measurable_space α]
  (μ : set α → ℝ≥0∞) : Prop :=
(measure_preimage_smul [] : ∀ (c : M) ⦃s : set α⦄, measurable_set s → μ ((λ x, c • x) ⁻¹' s) = μ s)

namespace smul_invariant_measure

@[to_additive] instance zero [has_scalar M α] : smul_invariant_measure M α 0 := ⟨λ _ _ _, rfl⟩

@[to_additive]
instance zero_measure [has_scalar M α] : smul_invariant_measure M α (0 : measure α) :=
smul_invariant_measure.zero

@[to_additive] instance add [has_scalar M α] {μ ν : set α → ℝ≥0∞} [smul_invariant_measure M α μ]
  [smul_invariant_measure M α ν] : smul_invariant_measure M α (μ + ν) :=
⟨λ c s hs, show _ + _ = _ + _,
  from congr_arg2 (+) (measure_preimage_smul μ c hs) (measure_preimage_smul ν c hs)⟩

@[to_additive]
instance add_measure [has_scalar M α] {μ ν : measure α} [smul_invariant_measure M α μ]
  [smul_invariant_measure M α ν] : smul_invariant_measure M α (μ + ν : measure α) :=
smul_invariant_measure.add

end smul_invariant_measure

variables [group G] [mul_action G α] [measurable_space G] [has_measurable_smul G α]

@[simp, to_additive]
lemma map_smul (c : G) (μ : measure α . volume_tac) [smul_invariant_measure G α μ] :
  map ((•) c) μ = μ :=
ext $ λ s hs, (map_apply (measurable_const_smul c) hs).trans
  (smul_invariant_measure.measure_preimage_smul _ _ hs)

@[to_additive]
lemma measure_preserving_smul (c : G) (μ : measure α . volume_tac) [smul_invariant_measure G α μ] :
  measure_preserving ((•) c) μ μ :=
⟨measurable_const_smul c, map_smul c μ⟩

@[simp, to_additive] lemma measure_preimage_smul (c : G) (μ : measure α . volume_tac)
  [smul_invariant_measure G α μ] (s : set α) : μ ((•) c ⁻¹' s) = μ s :=
(measure_preserving_smul c μ).measure_preimage_emb (measurable_embedding_const_smul c) s

@[simp, to_additive] lemma measure_smul (c : G) (μ : measure α . volume_tac)
  [smul_invariant_measure G α μ] (s : set α) : μ (c • s) = μ s :=
by rw [← preimage_smul_inv, measure_preimage_smul]

variable (G)

@[to_additive]
lemma measure_pos_of_smul_invariant_of_dense_orbit_of_Lindelof_ne_zero [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  {K U : set α} (hd : ∀ x : α, dense (mul_action.orbit G x))
  (hK : ∀ U : set (set α), (∀ t ∈ U, is_open t) → K ⊆ ⋃₀ U → ∃ V ⊆ U, countable V ∧ K ⊆ ⋃₀ V)
  (hμK : μ K ≠ 0) (hU : is_open U) (hne : U.nonempty) : 0 < μ U :=
begin
  refine pos_iff_ne_zero.2 (λ hμU, hμK _),
  have : ∀ x, ∃ g : G, g • x ∈ U,
    from λ x, dense_range.exists_mem_open (hd x) hU hne,
  choose g hgU,
  rcases hK ((λ x, (•) (g x) ⁻¹' U) '' K)
    (ball_image_iff.2 $ λ x hx, hU.preimage $ continuous_id.const_smul _)
    (λ x hx, mem_sUnion.2 $ ⟨_, ⟨x, hx, rfl⟩, hgU x⟩)
    with ⟨V, hVU, hVc, hKV⟩,
  refine measure_mono_null hKV ((measure_sUnion_null_iff hVc).2 $ λ s hs, _),
  rcases hVU hs with ⟨x, hx, rfl⟩,
  rwa measure_preimage_smul
end

@[to_additive]
lemma measure_pos_of_smul_invariant_of_is_open [topological_space G] [topological_space α]
  {K U : set α} {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_pretransitive G α] (hK : is_compact K) (hμK : μ K ≠ 0) (hU : is_open U)
  (hne : U.nonempty) : 0 < μ U :=
begin
  refine measure_pos_of_smul_invariant_of_dense_orbit_of_Lindelof_ne_zero G
    (λ x, (mul_action.surjective_smul G x).dense_range) (λ U hUo hKU, _) hμK hU hne,
  rw sUnion_eq_Union at hKU,
  rcases hK.elim_finite_subcover coe (subtype.forall.2 hUo) hKU with ⟨t, hKt⟩,
  refine ⟨coe '' (t : set U), image_subset_iff.2 (λ x hx, x.2), t.countable_to_set.image _, _⟩,
  rwa sUnion_image
end

@[to_additive]
lemma measure_lt_top_of_is_compact_of_smul_invariant [topological_space α]
  {μ : measure α} [smul_invariant_measure G α μ] [

end measure_theory
