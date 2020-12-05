import combinatorics.simple_graph.basic
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
