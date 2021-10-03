/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.polyhedron

/-!
# The face lattice of a polyhedron
-/

variables {𝕜 E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {x : E}
  {X Y : finset E} {C : set E}

/-- Faces of a polytope form a complete lattice. -/
def complete_lattice_faces (P : polytope 𝕜 E) : complete_lattice P.faces :=
sorry
