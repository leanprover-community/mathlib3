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

section coloring
variables {G} {β : Type v} (f : coloring G β) (a : β)

def color_class (f : coloring G β) (a : β) : set V := set.preimage f.1 {a}

variables [fintype (color_class f a)]

def fin_color_class : finset V := (color_class f a).to_finset

end coloring

end simple_graph
