import combinatorics.simple_graph.basic

namespace simple_graph
universes u v
variables {V : Type u} (G : simple_graph V)

/--
A graph G is β-colorable if there is an assignment of elements of β to
vertices of G (allowing repetition) such that adjacent vertices have
distinct colors.
-/
@[ext]
structure coloring (β : Type v) :=
(color : V → β)
(valid : ∀ ⦃v w : V⦄, G.adj v w → color v ≠ color w)

/--
A graph G is β-colorable if there is a β-coloring.
-/
def colorable (β : Type v) : Prop := nonempty (coloring G β)

variables [fintype V] [decidable_eq V] (β : Type v) [fintype β]

noncomputable instance : fintype (coloring G β) :=
begin
  have h2 : fintype (V → β),
  { refine ⟨_, _⟩,
    apply fintype.pi_finset,
    intros v,
    exact finset.univ,
    intros f,
    finish },
  apply fintype.of_injective coloring.color,
  { ext1 },
  exact h2,
end

noncomputable def chromatic_polynomial (k : ℕ) : ℕ := fintype.card (coloring G (fin k))



end simple_graph
