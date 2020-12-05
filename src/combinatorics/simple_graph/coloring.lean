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
def colorable (β : Type v) : Prop := nonempty (coloring G β)

section coloring
variables {G} {β : Type v} (f : coloring G β) (a : β)

def color_class (f : coloring G β) (a : β) : set V := set.preimage f.1 {a}

@[simp]
lemma color_class_vert (v : V) (h : v ∈ (color_class f a)) : f.1 v = a :=
begin
  exact h,
end

variables [fintype (color_class f a)]

def fin_color_class : finset V := (color_class f a).to_finset

end coloring

def bipartite (G : simple_graph V) : Prop :=
  colorable G (fin 2)

section bipartite
variables [bipartite G] (f : G.coloring (fin 2))

lemma endpoints {v w : V} (hadj : G.adj v w) (hv : v ∈ (color_class f (0 : fin 2))) :
  w ∈ (color_class f (1 : fin 2)) :=
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



end bipartite

end simple_graph
