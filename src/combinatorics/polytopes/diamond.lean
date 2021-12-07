/-
Copyright (c) 2021 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import tactic.linarith
import .graded

variables {α β : Type*}

/-!
# Diamond orders

This file defines diamond orders. A diamond order is a ranked order where every two elements whose
grade differs by `2` have exactly two elements in between.
-/

/-- A diamond order is a ranked order which has the diamond property: Every two elements whose grade
differs by `2` have exactly two elements in between. -/
class diamond_order (α : Type*) [preorder α] [order_bot α] extends grade_order α :=
(diamond {a b : α} (hab : a < b) (h : grade b = grade a + 2) : ∃ x y, x ≠ y ∧ set.Ioo a b = {x, y})

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
    change grade (⊤ : α) - grade b = grade (⊤ : α) - grade a + 2 at h,
    linarith [grade_le_grade_top a, grade_le_grade_top b],
  end
  .. order_dual.grade_order α }

/-- An order with one element is a diamond order, aka a nullitope. -/
def unique.to_diamond_order [unique α] [preorder α] [order_bot α] : diamond_order α :=
{ diamond := λ a b h, (h.ne $ subsingleton.elim _ _).elim,
  .. unique.to_graded_order α }

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
  .. is_simple_order.to_graded_order α }
