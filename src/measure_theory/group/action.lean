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
open measure_theory measure_theory.measure

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

end measure_theory
