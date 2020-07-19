import data.fintype.basic

open_locale classical
open finset
noncomputable theory

universe u

variable (V : Type u)

structure simple_graph :=
(E : V → V → Prop)
(loopless : irreflexive E)
(undirected : symmetric E)


namespace simple_graph
variables {V} (G : simple_graph V)

@[simp] lemma irrefl {v : V} : ¬ G.E v v := G.loopless v

variable [fintype V]

def neighbors (v : V) : finset V := univ.filter (G.E v)

@[simp] lemma neighbor_iff_adjacent (v w : V) :
 w ∈ neighbors G v ↔ G.E v w := by { unfold neighbors, simp }

def degree (v : V) : ℕ := (neighbors G v).card

def regular_graph (d : ℕ) : Prop :=
 ∀ v : V, degree G v = d

lemma edge_symm (u v : V) : G.E u v ↔ G.E v u :=
by split; apply G.undirected


lemma ne_of_edge {a b : V} (hab : G.E a b) : a ≠ b :=
begin
  intro h, rw h at hab, apply G.loopless b, exact hab,
end

end simple_graph
