/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.hull

/-!
# To move
-/

open set

variables {𝕜 E ι : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {s X Y : set E}

-- can be proven from the stuff about closure operators
lemma convex_hull_convex_hull_union :
  convex_hull 𝕜 (convex_hull 𝕜 X ∪ Y) = convex_hull 𝕜 (X ∪ Y) :=
subset.antisymm (convex_hull_min (union_subset (convex_hull_mono (subset_union_left X Y))
  (subset.trans (subset_convex_hull 𝕜 Y) (convex_hull_mono (subset_union_right X Y))))
  (convex_convex_hull 𝕜 _)) (convex_hull_mono (union_subset_union_left _ (subset_convex_hull 𝕜 _)))

-- can be proven from the stuff about closure operators
lemma convex_hull_self_union_convex_hull :
  convex_hull 𝕜 (X ∪ convex_hull 𝕜 Y) = convex_hull 𝕜 (X ∪ Y) :=
begin
  rw [union_comm, union_comm X Y],
  exact convex_hull_convex_hull_union,
end

lemma eq_left_or_right_or_mem_open_segment_of_mem_segment {x y z : E} (hz : z ∈ segment 𝕜 x y) :
  z = x ∨ z = y ∨ z ∈ open_segment 𝕜 x y :=
begin
   obtain ⟨a, b, ha, hb, hab, hz⟩ := hz,
  by_cases ha' : a = 0,
  swap,
  by_cases hb' : b = 0,
  swap,
  { right, right, exact ⟨a, b, ha.lt_of_ne (ne.symm ha'), hb.lt_of_ne (ne.symm hb'), hab, hz⟩ },
  all_goals { simp only [*, add_zero, not_not, one_smul, zero_smul, zero_add, rfl] at *},
  { left,
    refl },
  right,
  left,
  refl,
end
