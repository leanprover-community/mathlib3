import analysis.convex.topology
import topology.basic
import order.directed


variables {E : Type*} [add_comm_group E] [module ℝ E] {s X Y : set E}

open set

@[simp] lemma convex_hull_nonempty_iff :
  (convex_hull s).nonempty ↔ s.nonempty :=
begin
  rw [←ne_empty_iff_nonempty, ←ne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

--TODO: move to mathlib
lemma convex_sUnion_of_directed {c : set (set E)} (hcdirected : directed_on has_subset.subset c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → convex A) :
  convex (⋃₀c) :=
begin
  rw convex_iff_segment_subset,
  rintro x y hx hy z hz,
  rw mem_sUnion at ⊢ hx hy,
  obtain ⟨X, hX, hx⟩ := hx,
  obtain ⟨Y, hY, hy⟩ := hy,
  obtain ⟨Z, hZ, hXZ, hYZ⟩ := hcdirected X hX Y hY,
  exact ⟨Z, hZ, convex_iff_segment_subset.1 (hc hZ) (hXZ hx) (hYZ hy) hz⟩,
end

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

theorem convex_open_segment (a b : E) :
convex (open_segment a b) :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λz : E, a + z) ∘ (λ t : ℝ, t • (b - a)) := rfl,
  rw [open_segment_eq_image', this, image_comp],
  refine ((convex_Ioo _ _).is_linear_image _).translate _,
  exact is_linear_map.is_linear_map_smul' _,
end

--TODO: Generalise to LCTVS
variables [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
