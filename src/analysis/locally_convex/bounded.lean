/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.normed.normed_field
import analysis.seminorm
import topology.algebra.module.basic
import topology.bornology.basic

/-!
# Von Neumann Boundedness

This file defines von Neumann bounded sets and proves elementary properties.

## Main declarations

* `is_bounded`: A set `s` is bounded if every neighborhood of zero absorbs `s`.

## Main results

* `bounded_bornology`: The set of bounded sets forms a bornology.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

variables {𝕜 E : Type*}

open_locale topological_space pointwise

/-def is_bounded (𝕜) [semi_normed_ring 𝕜] [has_scalar 𝕜 E]
  [topological_space E] [has_zero E] (B : set E) : Prop :=
∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 B V-/

section semi_normed_ring

variables (𝕜)
variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E]
--variables (s : set E)

/-- A set `B` is bounded if every neighborhood of 0 absorbs `B`. -/
def is_bounded (B : set E) : Prop := ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V B

variables (E)

@[simp] lemma is_bounded_empty : is_bounded 𝕜 (∅ : set E) :=
λ _ _, absorbs_empty

variables {𝕜 E}

lemma is_bounded_iff (B : set E) : is_bounded 𝕜 B ↔ ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V B := iff.rfl

/-- If a topology is coarser, then it has more bounded sets. -/
lemma is_bounded_of_topological_space_le (t t' : topological_space E) (h : t ≤ t') {B : set E}
  (hB : @is_bounded 𝕜 E _ _ _ t B) : @is_bounded 𝕜 E _ _ _ t' B :=
λ V hV, hB V $ (le_iff_nhds t t').mp h 0 hV

lemma is_bounded_subset {B s : set E} (hB : is_bounded 𝕜 B) (hs : s ⊆ B) : is_bounded 𝕜 s :=
λ V hV, absorbs.mono_right (hB V hV) hs

lemma is_bounded_union {B₁ B₂ : set E} (hB₁ : is_bounded 𝕜 B₁) (hB₂ : is_bounded 𝕜 B₂):
is_bounded 𝕜 (B₁ ∪ B₂) :=
λ V hV, absorbs.union (hB₁ V hV) (hB₂ V hV)

end semi_normed_ring

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Singletons are bounded. -/
lemma is_bounded_singleton (x : E) : is_bounded 𝕜 ({x} : set E) :=
λ V hV, absorbent.absorbs (absorbent_nhds_zero hV)

lemma is_bounded_covers : ⋃₀ (set_of (is_bounded 𝕜)) = (set.univ : set E) :=
set.eq_univ_iff_forall.mpr (λ x, set.mem_sUnion.mpr
  ⟨{x}, is_bounded_singleton _, set.mem_singleton _⟩)

-- We do not make this an instance because there is the definitionally unequal notion of metric
-- bornology
def bounded_bornology : bornology E :=
bornology.of_bounded (set_of (is_bounded 𝕜)) (is_bounded_empty 𝕜 E)
  (λ _ hB _, is_bounded_subset hB) (λ _ hB _, is_bounded_union hB) is_bounded_covers

-- Todo:
-- suffices for V in a basis
-- can assume that V is balanced
-- totally bounded implies bounded
-- minimize assumptions for elementary properties


end normed_field
