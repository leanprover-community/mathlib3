/-
Copyright (c) 2021 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import .basic
import .diamond

/-!
# Polytope orders
-/

variables {α β : Type*}

/-- A polytope is a strongly connected diamond order. -/
class polytope_order (α : Type*) [partial_order α] [order_bot α] [locally_finite_order α]
  (n : out_param ℕ)
  extends diamond_order α n :=
(scon : graded.strong_connected α)

variables (α)

/-- An order with one element is a diamond order, aka a nullitope. -/
def subsingleton.to_polytope_order [subsingleton α] [partial_order α] [bounded_order α]
  [locally_finite_order α] (n : ℕ) :
  polytope_order α n :=
{ scon := by { apply graded.scon_of_grade_le_two, exact zero_le_two },
  .. subsingleton.to_diamond_order _ _ }

/-- A simple order is a diamond order, aka a point. -/
def is_simple_order.to_polytope_order [decidable_eq α] [partial_order α] [bounded_order α]
  [locally_finite_order α] [is_simple_order α] (n : ℕ) :
  polytope_order α n :=
{ scon := begin
    apply graded.scon_of_grade_le_two,
    rw is_simple_order.grade_top,
    exact one_le_two,
  end,
  .. is_simple_order.to_diamond_order _ _ }
