/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.measurable_equiv
import measure_theory.measure.regular
import dynamics.ergodic.measure_preserving
import dynamics.minimal

/-!
-/

open_locale ennreal pointwise topological_space
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

@[simp, to_additive] lemma measure_smul_set (c : G) (μ : measure α . volume_tac)
  [smul_invariant_measure G α μ] (s : set α) : μ (c • s) = μ s :=
by rw [← preimage_smul_inv, measure_preimage_smul]

variable (G)

@[to_additive] lemma measure_is_open_pos_of_smul_invariant_of_compact_ne_zero [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_minimal G α] {K U : set α} (hK : is_compact K) (hμK : μ K ≠ 0)
  (hU : is_open U) (hne : U.nonempty) : 0 < μ U :=
let ⟨t, ht⟩ := mul_action.exists_finite_cover_smul G hK hU hne
in pos_iff_ne_zero.2 $ λ hμU, hμK $ measure_mono_null ht $
  (measure_bUnion_null_iff t.countable_to_set).2 $ λ _ _, by rwa measure_smul_set

@[to_additive] lemma measure_is_open_pos_of_smul_invariant_of_ne_zero [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_minimal G α] [μ.regular] {U : set α} (hμ : μ ≠ 0)
  (hU : is_open U) (hne : U.nonempty) : 0 < μ U :=
let ⟨K, hK, hμK⟩ := regular.exists_compact_not_null.mpr hμ
in measure_is_open_pos_of_smul_invariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive] lemma measure_pos_iff_nonempty_of_smul_invariant [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_minimal G α] [μ.regular] {U : set α} (hμ : μ ≠ 0)
  (hU : is_open U) : 0 < μ U ↔ U.nonempty :=
⟨λ h, nonempty_of_measure_ne_zero h.ne', measure_is_open_pos_of_smul_invariant_of_ne_zero G hμ hU⟩

@[to_additive] lemma measure_eq_zero_iff_eq_empty_of_smul_invariant [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_minimal G α] [μ.regular] {U : set α} (hμ : μ ≠ 0)
  (hU : is_open U) : μ U = 0 ↔ U = ∅ :=
by rw [← not_iff_not, ← ne.def, ← pos_iff_ne_zero,
  measure_pos_iff_nonempty_of_smul_invariant G hμ hU, ← ne_empty_iff_nonempty]

@[to_additive] lemma is_locally_finite_measure_of_smul_invariant [topological_space G]
  [topological_space α] {μ : measure α} [smul_invariant_measure G α μ] [has_continuous_smul G α]
  [mul_action.is_minimal G α] {U : set α} (hU : is_open U) (hne : U.nonempty) (hμU : μ U ≠ ∞) :
  is_locally_finite_measure μ :=
⟨λ x, let ⟨g, hg⟩ := mul_action.exists_smul_mem_open G x hU hne in
  ⟨(•) g ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg, ne.lt_top $
    by rwa [measure_preimage_smul]⟩⟩

end measure_theory
