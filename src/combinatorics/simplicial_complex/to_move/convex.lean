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

--TODO: Generalise to LCTVS
variables [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
