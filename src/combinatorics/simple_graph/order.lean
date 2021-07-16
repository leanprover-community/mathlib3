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

instance : boolean_algebra (simple_graph V) :=
{ le := is_subgraph,
  sup := simple_graph.union,
  inf := simple_graph.inter,
  compl := simple_graph.compl,
  sdiff := simple_graph.sdiff,
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x v w h, x.ne_of_adj h,
  bot_le := λ x v w h, h.elim,
  sup_le := λ x y z hxy hyz v w h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  sdiff_eq := λ x y, by { ext v w, refine ⟨λ h, ⟨h.1, ⟨_, h.2⟩⟩, λ h, ⟨h.1, h.2.2⟩⟩,
                          rintro rfl, exact x.loopless _ h.1 },
  sup_inf_sdiff := λ a b, by { ext v w, refine ⟨λ h, _, λ h', _⟩,
                               obtain ⟨ha, _⟩|⟨ha, _⟩ := h; exact ha,
                               by_cases b.adj v w; exact or.inl ⟨h', h⟩ <|> exact or.inr ⟨h', h⟩ },
  inf_inf_sdiff := λ a b, by { ext v w, exact ⟨λ ⟨⟨_, hb⟩,⟨_, hb'⟩⟩, hb' hb, λ h, h.elim⟩ },
  le_sup_left := λ x y v w h, or.inl h,
  le_sup_right := λ x y v w h, or.inr h,
  le_inf := λ x y z hxy hyz v w h, ⟨hxy h, hyz h⟩,
  le_sup_inf := λ a b c v w h, or.dcases_on h.2 or.inl $
    or.dcases_on h.1 (λ h _, or.inl h) $ λ hb hc, or.inr ⟨hb, hc⟩,
  inf_compl_le_bot := λ a v w h, false.elim $ h.2.2 h.1,
  top_le_sup_compl := λ a v w ne, by {by_cases a.adj v w, exact or.inl h, exact or.inr ⟨ne, h⟩},
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
