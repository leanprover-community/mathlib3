import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.hom
import tactic.fin_cases

namespace simple_graph
universes u v
variables {V : Type u} (G : simple_graph V)

/-- A graph `G` is `β`-colorable if there is an assignment of elements of `β` to
vertices of `G` (allowing repetition) such that adjacent vertices have
distinct colors. -/
@[ext]
structure coloring (β : Type v) :=
(color : V → β)
(valid : ∀ ⦃v w : V⦄, G.adj v w → color v ≠ color w)

/-- A graph `G` is `β`-colorable if there is a `β`-coloring. -/
def colorable (β : Type v) : Prop := nonempty (G.coloring β)

namespace coloring
variables {G} {β : Type v} (f : G.coloring β)

/-- Given the mere existence of a `β`-coloring, extract it. -/
noncomputable def some_coloring (h : G.colorable β) : G.coloring β := classical.choice h

/-- The set of vertices with the given color. -/
def color_set (c : β) : set V := f.color ⁻¹' {c}

def color_finset (c : β) [fintype (f.color_set c)] : finset V := (f.color_set c).to_finset

@[simp]
lemma mem_color_set_iff (c : β) (v : V) : v ∈ f.color_set c ↔ f.color v = c :=
iff.rfl

/--
If `V` is a `fintype` with `decidable_eq`, then this gives that `color_class f c` is a `fintype`.
-/
instance color_class.decidable_pred (c : β) [decidable_eq β] : decidable_pred (f.color_set c) :=
by { intro v, change decidable (f.color v = c), apply_instance }

end coloring

/--
Given a coloring and a larger set of colors, one can extend the coloring set.
-/
def extend_coloring {β β' : Type*} (f : β ↪ β') : coloring G β ↪ coloring G β' :=
{ to_fun := λ F,
  { color := λ v, f (F.color v),
    valid := λ v w h hc, F.valid h (f.injective hc) },
  inj' := λ F F' h,
  begin
    ext,
    apply f.injective,
    simp only at h,
    exact congr_fun h x,
  end }

/--
Given a `β`-coloring of `G'` and an embedding of `G` into `G'`, one may restrict the coloring
to `G`.
-/
def restrict_coloring {G G' : simple_graph V} (f : G →g G') [hom.mono f]
  {β : Type v} (F : coloring G' β) : coloring G β :=
{ color := λ v, F.color (f v),
  valid := λ v w h hF, F.valid (f.map_adj h) hF }

/--
Given a coloring of a graph, one may restrict the coloring to a subgraph.
-/
def restrict_coloring_subgraph {β : Type*} (G' : subgraph G) (F : coloring G β) :
  coloring G'.coe β :=
{ color := λ v, F.color v,
  valid := λ v w h hF, F.valid (G'.adj_sub h) hF }

/--
A `colorable G α` graph is an `α`-partite graph, so we define bipartite as `colorable G (fin 2)`.
-/
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

/-- A partial coloring is a coloring where vertices in a given subset cannot be the same color if
adjacent. -/
structure partial_coloring (β : Type v) :=
(verts : set V)
(color : V → β)
(valid : ∀ ⦃v w : V⦄, v ∈ verts → w ∈ verts → G.adj v w → color v ≠ color w)

def partial_bipartition (G : simple_graph V) := G.partial_coloring (fin 2)

variables {G} {β : Type v}

def coloring.to_partial (f : G.coloring β) : G.partial_coloring β :=
{ verts := set.univ,
  color := f.color,
  valid := λ v w hv hw hadj, f.valid hadj }

variables (f : G.partial_coloring β)

def partial_coloring.restrict (V' : set V) (h : V' ⊆ f.verts) :
  G.partial_coloring β :=
{ verts := V',
  color := f.color,
  valid := λ v w hv hw, f.valid (h hv) (h hw) }

/-- The set of vertices with the given color. -/
def partial_coloring.color_set (c : β) : set V := f.verts ∩ f.color ⁻¹' {c}

end simple_graph
