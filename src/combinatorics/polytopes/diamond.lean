/-
Copyright (c) 2021 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import tactic.linarith
import order.locally_finite
import .graded

variables {α β : Type*}

/-!
# Diamond orders

This file defines diamond orders. An `n`-diamond order is a graded order where every two elements
whose grades differ by `2` have exactly `n` elements in between. Linear orders are `1`-diamond
orders. Preorders satisfying the usual diamond condition are `2`-diamond orders.
-/

/-- A diamond order is a graded order where every two elements whose grades differ by `2` have
exactly `n` elements in between. -/
class diamond_order (α : Type*) [preorder α] [order_bot α] [locally_finite_order α]
  (n : out_param ℕ) extends grade_order α :=
(diamond {a b : α} (hab : a ≤ b) (h : grade b = grade a + 2) : (finset.Ioo a b).card = n)

def diamond_of_linear [preorder α] [order_bot α] [linear_order α] [grade_order α]
  [locally_finite_order α] : diamond_order α 1 :=
⟨λ a b hab h, begin
  rw finset.card_eq_one,
  have := ex_unique_of_grade,
end⟩

lemma exists_pair_Ioo_of_lt [preorder α] [order_bot α] [diamond_order α] {a b : α} (hab : a < b)
  (h : grade b = grade a + 2) : ∃ x y, x ≠ y ∧ set.Ioo a b = {x, y} :=
diamond_order.diamond hab h

alias exists_pair_Ioo_of_lt ← has_lt.lt.exists_pair_Ioo

variables (α)

/-! ### Instances -/

/-- The dual of a diamond order. -/
instance [partial_order α] [bounded_order α] [diamond_order α] : diamond_order (order_dual α) :=
{ diamond := λ (a b : α) (hab : b < a) h, begin
    obtain ⟨x, y, hne, hxy⟩ := hab.exists_pair_Ioo _,
    exact ⟨x, y, hne, set.dual_Ioo.trans hxy⟩,
    change grade ⊤ - grade b = grade ⊤ - grade a + 2 at h,
    linarith [grade_le_grade_top a, grade_le_grade_top b],
  end
  .. order_dual.grade_order α }

/-- An order with one element is a diamond order, aka a nullitope. -/
def unique.to_diamond_order [unique α] [preorder α] [order_bot α] : diamond_order α :=
{ diamond := λ a b h, (h.ne $ subsingleton.elim _ _).elim,
  .. unique.to_grade_order α }

/-- A simple order is a diamond order, aka a point. -/
def is_simple_order.to_diamond_order [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] :
  diamond_order α :=
{ diamond := λ a b hab h, begin
    change grade _ = grade _ + 2 at h,
    rw [is_simple_order.eq_bot_of_lt hab, is_simple_order.eq_top_of_lt hab, grade_bot,
      is_simple_order.grade_top, zero_add] at h,
    linarith,
  end,
  .. is_simple_order.to_grade_order α }
