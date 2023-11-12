/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.prod
import data.fin.succ_pred
import order.succ_pred.relation

/-!
# The Hasse diagram as a graph

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the Hasse diagram of an order (graph of `covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `simple_graph.hasse`: Hasse diagram of an order.
* `simple_graph.path_graph`: Path graph on `n` vertices.
-/

open order order_dual relation

namespace simple_graph
variables (α β : Type*)

section preorder
variables [preorder α] [preorder β]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : simple_graph α :=
{ adj := λ a b, a ⋖ b ∨ b ⋖ a,
  symm := λ a b, or.symm,
  loopless := λ a h, h.elim (irrefl _) (irrefl _) }

variables {α β} {a b : α}

@[simp] lemma hasse_adj : (hasse α).adj a b ↔ a ⋖ b ∨ b ⋖ a := iff.rfl

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasse_dual_iso : hasse αᵒᵈ ≃g hasse α :=
{ map_rel_iff' := λ a b, by simp [or_comm],
  ..of_dual }

@[simp] lemma hasse_dual_iso_apply (a : αᵒᵈ) : hasse_dual_iso a = of_dual a := rfl
@[simp] lemma hasse_dual_iso_symm_apply (a : α) : hasse_dual_iso.symm a = to_dual a := rfl

end preorder

section partial_order
variables [partial_order α] [partial_order β]

@[simp] lemma hasse_prod : hasse (α × β) = hasse α □ hasse β :=
by { ext x y, simp_rw [box_prod_adj, hasse_adj, prod.covby_iff, or_and_distrib_right,
  @eq_comm _ y.1, @eq_comm _ y.2, or_or_or_comm] }

end partial_order

section linear_order
variables [linear_order α]

lemma hasse_preconnected_of_succ [succ_order α] [is_succ_archimedean α] : (hasse α).preconnected :=
λ a b, begin
  rw reachable_iff_refl_trans_gen,
  exact refl_trans_gen_of_succ _ (λ c hc, or.inl $ covby_succ_of_not_is_max hc.2.not_is_max)
    (λ c hc, or.inr $ covby_succ_of_not_is_max hc.2.not_is_max),
end

lemma hasse_preconnected_of_pred [pred_order α] [is_pred_archimedean α] : (hasse α).preconnected :=
λ a b, begin
  rw [reachable_iff_refl_trans_gen, ←refl_trans_gen_swap],
  exact refl_trans_gen_of_pred _ (λ c hc, or.inl $ pred_covby_of_not_is_min hc.1.not_is_min)
    (λ c hc, or.inr $ pred_covby_of_not_is_min hc.1.not_is_min),
end

end linear_order

/-- The path graph on `n` vertices. -/
def path_graph (n : ℕ) : simple_graph (fin n) := hasse _

lemma path_graph_preconnected (n : ℕ) : (path_graph n).preconnected := hasse_preconnected_of_succ _
lemma path_graph_connected (n : ℕ) : (path_graph (n + 1)).connected := ⟨path_graph_preconnected _⟩

end simple_graph
