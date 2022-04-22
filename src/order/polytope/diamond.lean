/-
Copyright (c) 2022 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import order.locally_finite
import tactic.linarith
import .grade

variables {α β : Type*} {n : ℕ}

/-!
# Diamond orders

This file defines diamond orders. An `n`-diamond order is a graded order where every two elements
whose grades differ by `2` have exactly `n` elements in between. Linear orders are `1`-diamond
orders. Preorders satisfying the usual diamond condition are `2`-diamond orders.
-/

/-- A diamond order is a graded order where every two elements whose grades differ by `2` have
exactly `n` elements in between. -/
class diamond_order (α : Type*) [preorder α] [order_bot α] [locally_finite_order α]
  (n : out_param ℕ) extends grade_order ℕ α :=
(diamond {a b : α} (hab : a ≤ b) (h : grade b = grade a + 2) : (finset.Ioo a b).card = n)

def diamond_of_linear [preorder α] [order_bot α] [linear_order α] [grade_order ℕ α]
  [locally_finite_order α] :
  diamond_order α 1 :=
⟨λ a b hab h, begin
  rw finset.card_eq_one,
  -- have := ex_unique_of_grade,
  sorry
end⟩

lemma card_Ioo_of_grade_eq [preorder α] [order_bot α] [locally_finite_order α] [diamond_order α n]
  {a b : α} (hab : a ≤ b) (h : grade ℕ b = grade ℕ a + 2) :
  (finset.Ioo a b).card = n :=
diamond_order.diamond hab h

lemma card_Ico_of_grade_eq [preorder α] [order_bot α] [locally_finite_order α] [diamond_order α n]
  {a b : α} (hab : a ≤ b) (h : grade ℕ b = grade ℕ a + 2) :
  (finset.Ico a b).card = n + 1:=
sorry

lemma card_Ioc_of_grade_eq [preorder α] [order_bot α] [locally_finite_order α] [diamond_order α n]
  {a b : α} (hab : a ≤ b) (h : grade ℕ b = grade ℕ a + 2) :
  (finset.Ioc a b).card = n + 1 :=
sorry

lemma card_Icc_of_grade_eq [preorder α] [order_bot α] [locally_finite_order α] [diamond_order α n]
  {a b : α} (hab : a ≤ b) (h : grade ℕ b = grade ℕ a + 2) :
  (finset.Icc a b).card = n + 2 :=
sorry

alias card_Icc_of_grade_eq ← has_le.le.card_Icc
alias card_Ico_of_grade_eq ← has_le.le.card_Ico
alias card_Ioc_of_grade_eq ← has_le.le.card_Ioc
alias card_Ioo_of_grade_eq ← has_le.le.card_Ioo

variables (α)

/-! ### Instances -/

-- instance order_dual.diamond_order [partial_order α] [bounded_order α] [locally_finite_order α]
--   [diamond_order α n] :
--   diamond_order (order_dual α) n :=
-- { diamond := λ a b hab (h : grade (order_dual ℕ) b = grade _ a + 2), begin
--     rw [card_Ioo, hab.of_dual.card_Ioo],
--     rw [grade_of_dual, grade_of_dual, ←grade_top_dual, ←nat.sub_add_comm (grade_le_grade_top _),
--       h, add_tsub_add_eq_tsub_right],
--   end,
--   .. order_dual.grade_order }

/-- An order with one element is a diamond order, aka a nullitope. -/
def subsingleton.to_diamond_order [subsingleton α] [preorder α] [order_bot α]
  [locally_finite_order α] (n : ℕ) :
  diamond_order α n :=
{ diamond := λ a b _ h, begin
    rw [subsingleton.elim a b, self_eq_add_right] at h,
    exact (two_ne_zero h).elim,
  end,
  .. subsingleton.to_grade_min_order }

/-- A simple order is a diamond order, aka a point. -/
def is_simple_order.to_diamond_order [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] [locally_finite_order α] (n : ℕ) :
  diamond_order α n :=
{ diamond := λ a b hab h, begin
    change grade _ _ = grade _ _ + 2 at h,
    letI := is_simple_order.to_grade_order α,
    have := is_simple_order.grade_le_one b,
    sorry
    -- rw [is_simple_order.eq_bot_of_lt hab, is_simple_order.eq_top_of_lt hab, grade_bot,
    --   is_simple_order.grade_top, zero_add] at h,
    -- linarith,
  end,
  .. is_simple_order.to_grade_order _ }
