/-
Copyright (c) 2021 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import combinatorics.simple_graph.subgraph

/-!
# Order relation on simple graphs

This file gives `simple_graph` a `bounded_lattice` instance under the `is_subgraph` relation, and
proves a couple lemmata about how this relation interacts with `simple_graph.subgraph.spanning_coe`.

# Main definitions:

* `simple_graph.is_subgraph`: A `simple_graph` is a subgraph of another if its `adj` is dominated by
  the other graph's.

* `bounded_lattice` instance: With this definition, `simple_graph` forms a `bounded_lattice`.

* `simple_graph.to_subgraph`: If a `simple_graph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `simple_graph.subgraph` type.

-/

namespace simple_graph

variable {V : Type*}

/-- The relation that one `simple_graph` is a subgraph of another. -/
def is_subgraph (x y : simple_graph V) : Prop := ∀ ⦃v w : V⦄, x.adj v w → y.adj v w

/-- The union of two `simple_graph`s. -/
def union (x y : simple_graph V) : simple_graph V :=
{ adj := x.adj ⊔ y.adj,
  sym := λ v w h, by rwa [sup_apply, sup_apply, x.adj_comm, y.adj_comm] }

/-- The intersection of two `simple_graph`s. -/
def inter (x y : simple_graph V) : simple_graph V :=
{ adj := x.adj ⊓ y.adj,
  sym := λ v w h, by rwa [inf_apply, inf_apply, x.adj_comm, y.adj_comm] }

instance : has_union (simple_graph V) := ⟨union⟩
instance : has_inter (simple_graph V) := ⟨inter⟩

instance : bounded_lattice (simple_graph V) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x v w h, x.ne_of_adj h,
  bot_le := λ x v w h, h.elim,
  sup_le := λ x y z hxy hyz v w h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  le_sup_left := λ x y v w h, or.inl h,
  le_sup_right := λ x y v w h, or.inr h,
  le_inf := λ x y z hxy hyz v w h, ⟨hxy h, hyz h⟩,
  inf_le_left := λ x y v w h, h.1,
  inf_le_right := λ x y v w h, h.2,
  .. partial_order.lift simple_graph.adj (λ (x y : simple_graph V) h, by { ext, rw h }) }

variable {G : simple_graph V}

/-- Turn a subgraph of a `simple_graph` into a member of its subgraph type. -/
@[simps] def to_subgraph (H : simple_graph V) (h : H ≤ G) :
G.subgraph :=
{ verts := set.univ,
  adj := H.adj,
  adj_sub := h,
  edge_vert := λ v w h, set.mem_univ v,
  sym := H.sym }

lemma to_subgraph.is_spanning (H : simple_graph V) (h : H ≤ G) :
(H.to_subgraph h).is_spanning := set.mem_univ

lemma subgraph.spanning_coe.is_subgraph_of_is_subgraph (H H' : subgraph G) (h : H ≤ H') :
H.spanning_coe ≤ H'.spanning_coe := h.2

end simple_graph
