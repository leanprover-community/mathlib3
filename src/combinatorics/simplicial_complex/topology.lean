/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.boundary
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.skeleton

/-!
# Topology of simplicial complexes
-/

open geometry set
open_locale affine big_operators classical

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [normed_linear_ordered_field 𝕜] [normed_group E] [normed_space 𝕜 E] {m n : ℕ}
  {S : simplicial_complex 𝕜 E} {X : finset E}

-- lemma boundary_space_eq_space_frontier_of_full_dimensional (hS : S.full_dimensional) :
--   S.boundary.space = frontier S.space := sorry

-- lemma boundary_face_iff_subset_space_frontier_of_full_dimensional (hS : S.full_dimensional) :
--   X ∈ S.boundary.faces ↔ X ∈ S.faces ∧ ↑X ⊆ frontier S.space :=
-- begin
--   split,
--   { rintro ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩,
--     use S.down_closed hY hXY,
--     sorry },
--   { rintro ⟨hX, hXspace⟩,
--     sorry }
-- end

lemma locally_finite.is_closed_space (hS : S.locally_finite) : is_closed S.space := sorry

lemma space_frontier_eq :
  frontier S.space = (⋃ (X ∈ S.facets) (H : (X : finset E).card ≤ finite_dimensional.finrank 𝕜 E),
  convex_hull 𝕜 ↑X) ∪ ⋃ (X ∈ S.boundary.faces), combi_interior 𝕜 X :=
sorry

-- lemma boundary_space_eq_of_full_dimensional (hS : S.full_dimensional) :
--   frontier S.space = S.boundary.space :=
-- begin
--   rw [space_frontier_eq, ←combi_interiors_cover],
--   sorry
-- end

/-- A simplicial complex is connected iff its space is. -/
def connected (S : simplicial_complex 𝕜 E) : Prop := connected_space S.space

/-- A simplicial complex is connected iff its 1-skeleton is. -/
lemma skeleton_one_connected : (S.skeleton 1).connected ↔ S.connected :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { sorry },
  { sorry }
end

lemma locally_compact_realisation_iff_locally_finite :
  locally_compact_space S.space ↔ S.locally_finite :=
begin
  rw locally_finite_iff_mem_finitely_many_faces,
  refine ⟨λ hS x, sorry, λ hS, locally_compact_of_compact_nhds _⟩,
  rintro ⟨x, hx⟩,
  specialize hS x,
  sorry
end

--def simplicial_complex.nonsingular (S : simplicial_complex 𝕜 E) {X : finset (fin m → 𝕜)} : Prop :=
-- homeomorph (S.link {X}).space (metric.ball (0 : E) 1)

end geometry.simplicial_complex
