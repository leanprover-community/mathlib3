/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import topology.basic
import order.directed


variables {E : Type*} [add_comm_group E] [module ℝ E] {s X Y : set E}

open set

--will be proven from the stuff about closure operators
lemma convex_hull_convex_hull_union :
  convex_hull (convex_hull X ∪ Y) = convex_hull (X ∪ Y) :=
subset.antisymm (convex_hull_min (union_subset (convex_hull_mono (subset_union_left X Y))
  (subset.trans (subset_convex_hull Y) (convex_hull_mono (subset_union_right X Y))))
  (convex_convex_hull _)) (convex_hull_mono (union_subset_union_left _ (subset_convex_hull _)))

--will be proven from the stuff about closure operators
lemma convex_hull_self_union_convex_hull :
  convex_hull (X ∪ convex_hull Y) = convex_hull (X ∪ Y) :=
begin
  rw [union_comm, union_comm X Y],
  exact convex_hull_convex_hull_union,
end

lemma eq_left_or_right_or_mem_open_segment_of_mem_segment {x y z : E} (hz : z ∈ segment x y) :
  z = x ∨ z = y ∨ z ∈ open_segment x y :=
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

lemma convex_hull_pair {a b : E} :
  convex_hull {a, b} = (segment a b) := sorry

--TODO: Generalise to LCTVS
variables [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
