import combinatorics.simple_graph.basic
import combinatorics.simple_graph.hom
open simple_graph

/-!
# Simple graphs on a given vertex type
-/

universes u v
variables {α : Type u}

namespace simple_graph_on

/--
A spanning subgraph is a graph containing all the vertices of the
other and a subset of its edges. This is the natural notion for graphs from `simple_graph_on`.
-/
def is_spanning_subgraph (x y : simple_graph_on α) : Prop := ∀ (v w : α), x.adj v w → y.adj v w

def union (x y : simple_graph_on α) : simple_graph_on α :=
{ adj := λ (v w : α), x.adj v w ∨ y.adj v w,
  symm' := λ v w h, by { cases h, left, exact x.symm' h, right, exact y.symm' h },
  loopless' := λ v h, by { cases h, apply x.loopless' _ h, apply y.loopless' _ h } }

def inter (x y : simple_graph_on α) : simple_graph_on α :=
{ adj := λ (v w : α), x.adj v w ∧ y.adj v w,
  symm' := λ v w h, ⟨x.symm' h.1, y.symm' h.2⟩,
  loopless' := λ v h, x.loopless' _ h.1 }

instance : bounded_lattice (simple_graph_on α) :=
{ le := is_spanning_subgraph,
  sup := union,
  inf := inter,
  bot := empty_graph α,
  top := complete_graph α,
  le_refl := by obviously,
  le_trans := by obviously,
  le_antisymm := by obviously,
  le_inf := by obviously,
  sup_le := by obviously,
  inf_le_left := by obviously,
  inf_le_right := by obviously,
  le_sup_left := λ G H, λ v w h, by { left, apply h, },
  le_sup_right := λ G H, λ v w h, by { right, apply h, },
  bot_le := by obviously,
  le_top := by { intro G, have h := G.loopless', obviously, }, }

/--
Erase an edge of a graph to get a smaller graph.
-/
def erase_edge (G : simple_graph_on α) {e : sym2 α} (h : e ∈ (↟G).edge_set) : simple_graph_on α :=
{ adj := λ v w, G.adj v w ∧ ¬ (v ∈ e ∧ w ∈ e),
  symm' := λ v w h, ⟨G.symm' h.1, by { rw and_comm, exact h.2, }⟩,
  loopless' := λ v h, by { have h := G.loopless' v, tidy } }

/--
A graph with a given vertex type and a single edge.
-/
def single_edge_graph {α : Type u} {v w : α} (hne : v ≠ w) : simple_graph_on α :=
{ adj := λ i j, (i = v ∧ j = w) ∨ (i = w ∧ j = v) }

/-- Add an edge between two distinct vertices. -/
def insert_edge (G : simple_graph_on α) {v w : α} (hne : v ≠ w) := G ⊔ single_edge_graph hne

end simple_graph_on
