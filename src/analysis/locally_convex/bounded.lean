/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.basic
import topology.bornology.basic

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `bornology.is_vonN_bounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
absorbs `s`.
* `bornology.vonN_bornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `bornology.is_vonN_bounded_of_topological_space_le`: A coarser topology admits more
von Neumann-bounded sets.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

variables {𝕜 E : Type*}

open_locale topological_space pointwise

namespace bornology

section semi_normed_ring

section has_zero

variables (𝕜)
variables [semi_normed_ring 𝕜] [has_scalar 𝕜 E] [has_zero E]
variables [topological_space E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def is_vonN_bounded (s : set E) : Prop := ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → absorbs 𝕜 V s

variables (E)

@[simp] lemma is_vonN_bounded_empty : is_vonN_bounded 𝕜 (∅ : set E) :=
λ _ _, absorbs_empty

variables {𝕜 E}

lemma is_vonN_bounded_iff (s : set E) : is_vonN_bounded 𝕜 s ↔ ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V s :=
iff.rfl

/-- Subsets of bounded sets are bounded. -/
lemma is_vonN_bounded.subset {s₁ s₂ : set E} (h : s₁ ⊆ s₂) (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 s₁ :=
λ V hV, (hs₂ hV).mono_right h

/-- The union of two bounded sets is bounded. -/
lemma is_vonN_bounded.union {s₁ s₂ : set E} (hs₁ : is_vonN_bounded 𝕜 s₁)
  (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 (s₁ ∪ s₂) :=
λ V hV, (hs₁ hV).union (hs₂ hV)

end has_zero

end semi_normed_ring

section multiple_topologies

variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
lemma is_vonN_bounded.of_topological_space_le {t t' : topological_space E} (h : t ≤ t') {s : set E}
  (hs : @is_vonN_bounded 𝕜 E _ _ _ t s) : @is_vonN_bounded 𝕜 E _ _ _ t' s :=
λ V hV, hs $ (le_iff_nhds t t').mp h 0 hV

end multiple_topologies

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Singletons are bounded. -/
lemma is_vonN_bounded_singleton (x : E) : is_vonN_bounded 𝕜 ({x} : set E) :=
λ V hV, (absorbent_nhds_zero hV).absorbs

/-- The union of all bounded set is the whole space. -/
lemma is_vonN_bounded_covers : ⋃₀ (set_of (is_vonN_bounded 𝕜)) = (set.univ : set E) :=
set.eq_univ_iff_forall.mpr (λ x, set.mem_sUnion.mpr
  ⟨{x}, is_vonN_bounded_singleton _, set.mem_singleton _⟩)

variables (𝕜 E)

/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology.-/
@[reducible] -- See note [reducible non-instances]
def vonN_bornology : bornology E :=
bornology.of_bounded (set_of (is_vonN_bounded 𝕜)) (is_vonN_bounded_empty 𝕜 E)
  (λ _ hs _ ht, hs.subset ht) (λ _ hs _, hs.union) is_vonN_bounded_covers

variables {E}

@[simp] lemma is_bounded_iff_is_vonN_bounded {s : set E} :
  @is_bounded _ (vonN_bornology 𝕜 E) s ↔ is_vonN_bounded 𝕜 s :=
is_bounded_of_bounded_iff _

end normed_field

end bornology
