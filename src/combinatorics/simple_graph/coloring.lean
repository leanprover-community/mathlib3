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

lemma color_set_disjoint (c c' : β) (hn : c ≠ c') : f.color_set c ∩ f.color_set c' = ∅ :=
begin
  ext,
  simp only [set.mem_empty_eq, mem_color_set_iff, set.mem_inter_eq, not_and, iff_false],
  rintro rfl,
  exact hn,
end

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

/-- This is an indexed family of disjoint subsets of the vertex type of `G` such that vertices in
the same set are not adjacent.  This is similar to `subgraph.coloring`, however not every vertex
needs to be given a color. -/
@[ext]
structure coloring' {V : Type u} (G : simple_graph V) (β : Type v) :=
(color_set : β → set V)
(disjoint : ∀ (c c' : β), c ≠ c' → color_set c ∩ color_set c' = ∅)
(valid : ∀ (c : β) (v v' : V), v ∈ color_set c → v' ∈ color_set c → ¬G.adj v v')

@[simps]
def coloring.to_coloring' {V : Type u} {G : simple_graph V} {β : Type v}
  (f : G.coloring β) : G.coloring' β :=
{ color_set := f.color_set,
  disjoint := f.color_set_disjoint,
  valid := λ c v v' hv hv' h, begin
    rw coloring.mem_color_set_iff at hv hv',
    rw ←hv' at hv,
    exact f.valid h hv,
  end }

section coloring'
variables {G} {β : Type v}

def empty : G.coloring' β :=
{ color_set := λ c, ∅,
  disjoint := by tidy,
  valid := by tidy }

def is_subcoloring (f f' : G.coloring' β) : Prop :=
∀ (c : β), f.color_set c ⊆ f'.color_set c

instance : has_subset (G.coloring' β) := ⟨is_subcoloring⟩

def inter (f f' : G.coloring' β) : G.coloring' β :=
{ color_set := λ c, f.color_set c ∩ f'.color_set c,
  disjoint := λ c c' hn, begin
    rw [set.inter_assoc, set.inter_comm (f'.color_set c),
        set.inter_assoc (f.color_set c'), ←set.inter_assoc,
        f.disjoint _ _ hn, f'.disjoint _ _ hn.symm],
    simp,
  end,
  valid := λ c v v' hv hv', f.valid c v v' hv.left hv'.left }

instance : has_inter (G.coloring' β) := ⟨inter⟩

instance subcoloring.semilattice_inf_bot : semilattice_inf_bot (G.coloring' β) :=
{ le := has_subset.subset,
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := λ f f' h h', by { ext1, exact funext (λ c, set.subset.antisymm (h c) (h' c)) },
  inf := has_inter.inter,
  le_inf := by tidy,
  inf_le_left := by tidy,
  inf_le_right := by tidy,
  bot := empty,
  bot_le := by tidy }

end coloring'

/-- A `bipartition'` is a bipartition of a subset of vertices.  This is implemented with
`G.coloring' (fin 2)` so bipartitions form a `semilattice_inf_bot`. -/
def bipartition' (G : simple_graph V) := G.coloring' (fin 2)

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
