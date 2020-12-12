import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.hom
import tactic.fin_cases

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
def colorable (β : Type v) : Prop := nonempty (G.coloring β)

namespace coloring
variables {G} {β : Type v} (f : G.coloring β)

noncomputable
def some_coloring (h : G.colorable β) : G.coloring β := classical.choice h

def color_set (c : β) : set V := f.color ⁻¹' {c}

def color_finset (c : β) [fintype (f.color_set c)] : finset V := (f.color_set c).to_finset

@[simp]
lemma mem_color_set_iff (c : β) (v : V) : v ∈ f.color_set c ↔ f.color v = c :=
by refl

/-- If `V` is a `fintype` with `decidable_eq`, then this gives that `color_class f c` is a `fintype`. -/
instance color_class.decidable_pred (c : β) [decidable_eq β] : decidable_pred (f.color_set c) :=
by { intro v, change decidable (f.color v = c), apply_instance }

end coloring

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
def restrict_coloring {G : simple_graph V} {G' : simple_graph V} (f : G →g G') [hom.mono f] {β : Type*} : coloring G' β → coloring G β :=
λ F, { color := λ v, F.color (f v),
       valid := begin
         rintros v w h hF,
         apply F.valid (f.map_adj h) hF,
       end }

/--
Given a coloring of a graph, one may restrict the coloring to a subgraph.
-/
def restrict_coloring_subgraph {β : Type*} (G' : subgraph G) : coloring G β → coloring G'.to_simple_graph β :=
restrict_coloring G'.map_top


/-- A `colorable G α` graph is an `α`-partite graph, so we define bipartite as `colorable G (fin 2)`. -/
def is_bipartite (G : simple_graph V) : Prop := G.colorable (fin 2)

abbreviation bipartition (G : simple_graph V) := G.coloring (fin 2)

section bipartite
variables (h : is_bipartite G) (f : G.coloring (fin 2))

/- I'm not sure this theorem is necessary -/
/-
lemma endpoints {v w : V} (hadj : G.adj v w) (hv : v ∈ color_class f 0) :
  w ∈ color_class f 1 :=
begin

  rw color_class,
  simp,
  rw color_class at hv,
  simp at hv,
  have hne := coloring.valid f hadj,
  rw hv at hne,
  /-ext,
  simp,
  cases (f.color w),
  have hne2 :  (0 : nat) ≠ val,

  have hge : 0 < val,-/

  --fin_cases (f.color w),
  --fin_cases a,
  sorry,
end
-/


end bipartite

end simple_graph
