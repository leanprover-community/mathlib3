/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.independent
import analysis.convex.topology
import analysis.normed_space.ordered

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier and intrinsic interior of a set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]
-/

open set
open_locale big_operators

variables {𝕜 E : Type*} [normed_linear_ordered_field 𝕜] [normed_group E] [normed_space 𝕜 E]
  {s t : set E} {x y : E}

variables (𝕜)

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
def intrinsic_interior (s : set E) : set E := coe '' interior ((coe : affine_span 𝕜 s → E) ⁻¹' s)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsic_frontier (s : set E) : set E := coe '' frontier ((coe : affine_span 𝕜 s → E) ⁻¹' s)

def intrinsic_closure (s : set E) : set E := coe '' closure {x : affine_span 𝕜 s | ↑x ∈ s}

variables {𝕜}

lemma intrinsic_interior_subset (s : set E) : intrinsic_interior 𝕜 s ⊆ s :=
image_subset_iff.2 interior_subset

lemma intrinsic_frontier_subset (hs : is_closed s) : intrinsic_frontier 𝕜 s ⊆ s :=
image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

@[simp] lemma intrinsic_interior_empty : intrinsic_interior 𝕜 (∅ : set E) = ∅ :=
subset_empty_iff.1 $ intrinsic_interior_subset _

@[simp] lemma intrinsic_frontier_empty : intrinsic_frontier 𝕜 (∅ : set E) = ∅ :=
subset_empty_iff.1 $ intrinsic_frontier_subset is_closed_empty

-- Prop 8.7 and 8.8
protected lemma set.nonempty.intrinsic_interior (hs : s.nonempty) (hs : convex 𝕜 s) :
  (intrinsic_interior 𝕜 s).nonempty :=
begin
  sorry
end

variables {𝕜}

lemma convex.open_segment_subset_intrinsic_interior_of_mem_left (hs : convex 𝕜 s)
  (x ∈ intrinsic_interior 𝕜 s) (y ∈ s) :
  open_segment 𝕜 x y ⊆ intrinsic_interior 𝕜 s :=
begin
  rintro z hz,
  split,
  { sorry },
  dsimp,
  --obtain ⟨x₁, x₂, hx₁, hx₂, x, ⟨hxA, ι, t, hw₀, hw₁, hyA, hy⟩, hx⟩ := sorry,
  sorry
end

@[simp] lemma intrinsic_interior_union_intrinsic_frontier :
  intrinsic_interior 𝕜 s ∪ intrinsic_frontier 𝕜 s = s := sorry

lemma is_extreme_intrinsic_frontier (hs : is_closed s) : is_extreme 𝕜 s (intrinsic_frontier 𝕜 s) :=
begin
  refine ⟨intrinsic_frontier_subset hs, λ x₁ hx₁ x₂ hx₂ x hxs hx, _⟩,
  sorry
end
