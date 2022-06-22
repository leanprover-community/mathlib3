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

This file defines the Hasse diagram of an order (graph of `covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `simple_graph.hasse`: Hasse diagram of an order.
* `simple_graph.path_graph`: Path graph on `n` vertices.
-/


namespace prod
variables {α β : Type*} [partial_order α] [partial_order β] {a a₁ a₂ : α}
  {b b₁ b₂ : β} {x y : α × β}

@[simp] lemma swap_le_swap_iff : x.swap ≤ y.swap ↔ x ≤ y := and_comm _ _

@[simp] lemma swap_lt_swap_iff : x.swap < y.swap ↔ x < y :=
lt_iff_lt_of_le_iff_le' swap_le_swap_iff swap_le_swap_iff

@[simp] lemma swap_covby_swap_iff : x.swap ⋖ y.swap ↔ x ⋖ y :=
apply_covby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

lemma mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ := and_iff_left le_rfl
lemma mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ := and_iff_right le_rfl

lemma mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

lemma mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

lemma fst_eq_or_snd_eq_of_covby : x ⋖ y → x.1 = y.1 ∨ x.2 = y.2 :=
begin
  refine λ h, of_not_not (λ hab, _),
  push_neg at hab,
  exact h.2 (mk_lt_mk.2 $ or.inl ⟨hab.1.lt_of_le h.1.1.1, le_rfl⟩)
    (mk_lt_mk.2 $ or.inr ⟨le_rfl, hab.2.lt_of_le h.1.1.2⟩),
end

lemma mk_covby_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a ⋖ a₂ :=
begin
  split;
  rintro ⟨hcov_left, hcov_right⟩;
  split;
  [ { skip },
    { intros c hac hca₂,
      apply @hcov_right (c, b) },
    { skip },
    { rintros ⟨c₁, c₂⟩ h h',
      apply @hcov_right c₁;
      have : c₂ = b := le_antisymm h'.1.2 h.1.2;
      rw this at *, } ];
  rw mk_lt_mk_iff_left at *;
  assumption,
end

lemma mk_covby_mk_iff_right : (a, b) ⋖ (a, b₂) ↔ b ⋖ b₂ :=
swap_covby_swap_iff.trans mk_covby_mk_iff_left

lemma covby_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain h₁ | h₂ := fst_eq_or_snd_eq_of_covby h,
    { rw [mk_covby_mk_iff_right] at *,
      tauto },
    { rw mk_covby_mk_iff_left at *,
      tauto } },
  { rcases h with ⟨acov, beq⟩ | ⟨aeq, bcov⟩,
    { rw beq at *,
      exact mk_covby_mk_iff_left.mpr acov },
    { rw aeq at *,
      exact mk_covby_mk_iff_right.mpr bcov } }
end

lemma _root_.is_min.prod_mk (ha : is_min a) (hb : is_min b) : is_min (a, b) :=
λ c hc, ⟨ha hc.1, hb hc.2⟩

lemma _root_.is_min.fst (hx : is_min x) : is_min x.1 :=
λ c hc, (hx ((and_iff_left le_rfl).2 hc : (c, x.2) ≤ x)).1

lemma _root_.is_min.snd (hx : is_min x) : is_min x.2 :=
λ c hc, (hx ((and_iff_right le_rfl).2 hc : (x.1, c) ≤ x)).2

lemma is_min_iff : is_min x ↔ is_min x.1 ∧ is_min x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

end prod

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
