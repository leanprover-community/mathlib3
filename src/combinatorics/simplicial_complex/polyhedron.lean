import combinatorics.simplicial_complex.exposed

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E} {C : set E}

/-- A polytope is an intersection of finitely many halfspaces. -/
@[ext] structure polytope (E : Type*) [normed_group E] [normed_space ℝ E] :=
(Hrepr : finset ((E →L[ℝ] ℝ) × ℝ))

instance : has_coe (polytope E) E := λ P, {x | ∀ l ∈ P.Hrepr, l.1 x ≤ l.2}

def polytope.faces (P : polytope E) : set (polytope E) := sorry

instance complete_lattice_polytopes : complete_lattice (polytope E) :=
sorry

/-- A polyhedron is the convex hull of a finite number of points. -/
@[ext] structure polyhedron (E : Type*) [normed_group E] [normed_space ℝ E] :=
(carrier : set E)
(verts : finset E)
(hcarrier : carrier = {x | ∀ l ∈ Hrepr, l.1 x ≤ l.2})

instance complete_lattice_polyhedrons : complete_lattice (polyhedron E) :=
sorry
