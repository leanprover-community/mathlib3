import combinatorics.simple_graph.hom
import combinatorics.simple_graph.subgraph

namespace simple_graph
universes u v
variables (G : simple_graph)

/--
A graph G is β-colorable if there is an assignment of elements of β to
vertices of G (allowing repetition) such that adjacent vertices have
distinct colors.
-/
@[ext]
structure coloring (β : Type v) :=
(color : V G → β)
(valid : ∀ ⦃v w : V G⦄, v ~g w → color v ≠ color w)

/--
A graph G is β-colorable if there is a β-coloring.
-/
def colorable (β : Type v) : Prop := nonempty (coloring G β)

/--
Given a coloring and a larger set of colors, one can extend the coloring set.
-/
def extend_coloring {β β' : Type*} (f : β ↪ β') : coloring G β ↪ coloring G β' :=
{ to_fun := λ F, { color := λ v, f (F.color v),
                   valid := begin
                     intros v w h hc, apply F.valid h, apply function.embedding.injective f, assumption,
                   end},
  inj' := begin intros F F' h, ext, apply function.embedding.injective f, simp at h, exact congr_fun h x, end
}

/--
Given a coloring and an embedding of a graph, one may restrict the coloring of the graph.
-/
def restrict_coloring {G : simple_graph} {G' : simple_graph} (f : G →g G') [hom.mono f] {β : Type*} : coloring G' β → coloring G β :=
λ F, { color := λ v, F.color (f v),
       valid := begin
         rintros v w h hF,
         apply F.valid (f.map_adj h) hF,
       end }

/--
Given a coloring of a graph, one may restrict the coloring to a subgraph.
-/
def restrict_coloring_subgraph {β : Type*} (G' : subgraph G) : coloring G β → coloring ↟G' β :=
restrict_coloring G'.map_top

/--
A complete graph is colorable by its own vertex type.  (This means that if its vertex type
has cardinality n, then it is n-colorable.)
-/
def complete_graph_coloring (V : Type u) : coloring ↟(complete_graph V) V :=
{ color := id,
  valid := by tidy }

lemma complete_graph_coloring_inj {V : Type u} [decidable_eq V] {β : Type v} (c : coloring ↟(complete_graph V) β) :
  function.injective c.color :=
begin
  intros v w h,
  cases c with color valid,
  dsimp at h,
  by_contra,
  apply valid a,
  exact h,
end

lemma complete_graph_min_colors {n m : ℕ} (c : coloring ↟(complete_graph (fin n)) (fin m)) : n ≤ m :=
begin
  have h := fintype.card_le_of_injective c.color (complete_graph_coloring_inj _),
  simpa using h,
end

def coloring_equiv_complete_graph_hom (β : Type v) : coloring G β ≃ (G →g ↟(complete_graph β)) :=
{ to_fun := λ c,
  { to_fun := c.color,
    map_rel' := λ v w a, coloring.valid c a },
  inv_fun := λ c,
    { color := c,
    valid := λ v w a, c.map_rel' a },
  left_inv := by tidy,
  right_inv := by tidy }


end simple_graph
