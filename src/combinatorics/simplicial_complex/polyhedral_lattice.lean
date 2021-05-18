import combinatorics.simplicial_complex.polyhedron

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E} {C : set E}

/-- Faces of a polytope form a complete lattice. -/
def complete_lattice_faces (P : polytope E) : complete_lattice P.faces :=
sorry
