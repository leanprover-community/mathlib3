/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.extreme
import analysis.convex.intrinsic

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier and intrinsic interior of a set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]
-/

open set
open_locale big_operators

variables {𝕜 E : Type*} [normed_linear_ordered_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
  {s t : set E} {x y : E}

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

lemma is_extreme_intrinsic_frontier (hs : is_closed s) : is_extreme 𝕜 s (intrinsic_frontier 𝕜 s) :=
begin
  refine ⟨intrinsic_frontier_subset hs, λ x₁ hx₁ x₂ hx₂ x hxs hx, _⟩,
  sorry
end
