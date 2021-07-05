/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.boundary
import combinatorics.simplicial_complex.skeleton

namespace affine

open_locale classical affine big_operators
open set
variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {X : finset E}

lemma boundary_space_eq_space_frontier_of_full_dimensional (hS : S.full_dimensional) :
  S.boundary.space = frontier S.space :=
begin
  ext x,
  split,
  {
    sorry,
  },
  {
    sorry
  }
end

lemma boundary_face_iff_subset_space_frontier_of_full_dimensional (hS : S.full_dimensional) :
  X ∈ S.boundary.faces ↔ X ∈ S.faces ∧ ↑X ⊆ frontier S.space :=
begin
  split,
  { rintro ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩,
    use S.down_closed hY hXY,
    sorry
  },
  { rintro ⟨hX, hXspace⟩,
    sorry
  }
end

lemma closed_space_of_locally_finite (hS : S.locally_finite) :
  is_closed S.space :=
begin
  sorry
end

lemma space_frontier_eq :
  frontier S.space = (⋃ (X ∈ S.facets) (H : (X : finset E).card ≤ finite_dimensional.finrank ℝ E),
  convex_hull ↑X) ∪ (⋃ (X ∈ S.boundary.faces), combi_interior X) :=
begin
  sorry
end

lemma boundary_space_eq_of_full_dimensional (hS : S.full_dimensional) :
  frontier S.space = S.boundary.space :=
begin
  rw space_frontier_eq,
  rw combi_interiors_cover,
  ext x,
  split,
  {
    sorry
  },
  sorry
end

/-A simplicial complex is connected iff its space is-/
def simplicial_complex.connected (S : simplicial_complex E) :
  Prop :=
connected_space S.space

/-A simplicial complex is connected iff its 1-skeleton is-/
lemma connected_iff_one_skeleton_connected :
  S.connected ↔ (S.skeleton 1).connected :=
begin
  split,
  { rintro h,
    unfold simplicial_complex.connected,
    sorry
  },
  {
    sorry
  }
end

lemma locally_compact_realisation_iff_locally_finite :
  S.locally_finite ↔ locally_compact_space S.space :=
begin
  rw locally_finite_iff_mem_finitely_many_faces,
  split,
  {
    rintro hS,
    apply locally_compact_of_compact_nhds,
    rintro ⟨x, hx⟩,
    specialize hS x,
    sorry
  },
  {
    rintro hS x,
    --obtain ⟨a, b⟩ := hS x,
    sorry
  }
end

--def simplicial_complex.nonsingular (S : simplicial_complex E) {X : finset (fin m → ℝ)} : Prop :=
--  homeomorph (S.link {X}).space (metric.ball (0 : E) 1)

end affine
