/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Violeta Hernández Palacios
-/
import combinatorics.polytopes.flag
import order.atoms

variables {α β : Type*}


section order_classes

/-- A diamond order is a ranked order which has the diamond property: Every two elements whose grade
differs by `2` have exactly two elements in between. -/
class diamond_order (α : Type*) [preorder α] [order_bot α] extends grade_order α :=
(diamond {a b : α} (hab : a < b) (h : grade b = grade a + 2) : ∃ x y, x ≠ y ∧ set.Ioo a b = {x, y})

lemma exists_pair_Ioo_of_lt [preorder α] [order_bot α] [diamond_order α] {a b : α} (hab : a < b)
  (h : grade b = grade a + 2) : ∃ x y, x ≠ y ∧ set.Ioo a b = {x, y} :=
diamond_order.diamond hab h

alias exists_pair_Ioo_of_lt ← has_lt.lt.exists_pair_Ioo

/-- A polytope is a strongly connected diamond order. -/
class polytope_order (α : Type*) [partial_order α] [order_bot α] extends diamond_order α :=
(scon : graded.strong_connected α)

end order_classes

universes u v

namespace polytope
variables (α)

/-- An order with one element is a graded order, aka a nullitope. -/
def unique.to_graded_order [unique α] [preorder α] [order_bot α] : grade_order α :=
{ grade := λ _, 0,
  grade_bot := rfl,
  strict_mono := subsingleton.strict_mono,
  hcovers := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim }

/-- A simple order is a graded order, aka a point. -/
def is_simple_order.to_graded_order [decidable_eq α] [preorder α] [bounded_order α]
  [is_simple_order α] :
  grade_order α :=
{ grade := λ a, if a = ⊥ then 0 else 1,
  grade_bot := if_pos rfl,
  strict_mono := λ a b h, begin
    convert zero_lt_one,
    { exact if_pos (is_simple_order.eq_bot_of_lt h) },
    { exact if_neg (ne_bot_of_lt h) },
    { apply_instance }
  end,
  hcovers := λ a b h, begin
    convert (zero_add 1).symm,
    { exact if_neg (ne_bot_of_lt h.1) },
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) }
  end }

variables {α}

lemma unique.grade_top [unique α] [preorder α] [bounded_order α] [grade_order α] :
  grade (⊤ : α) = 0 :=
(congr_arg _ $ subsingleton.elim _ _).trans grade_bot

lemma is_simple_order.grade_top [partial_order α] [bounded_order α] [is_simple_order α]
  [grade_order α] :
  grade (⊤ : α) = 1 :=
is_simple_order.bot_covers_top.grade.trans $ by rw [grade_bot, zero_add]

variables (α)

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

/-- An order with one element is a diamond order, aka a nullitope. -/
def unique.to_polytope_order [unique α] [partial_order α] [bounded_order α] : polytope_order α :=
{ scon := by apply graded.scon_of_grade_le_two; exact zero_le_two,
  .. unique.to_diamond_order α }

/-- A simple order is a diamond order, aka a point. -/
def is_simple_order.to_polytope_order [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] :
  polytope_order α :=
{ scon := begin
    apply graded.scon_of_grade_le_two,
    sorry
end,
  .. is_simple_order.to_diamond_order α }

/-- The dual of a diamond order. -/
instance (α : Type*) [partial_order α] [bounded_order α] [diamond_order α] :
  diamond_order (order_dual α) :=
⟨ begin
  rintro (a b : α) (hab : b < a) h,
  obtain ⟨x, y, hne, hxy⟩ := hab.exists_pair_Ioo _,
  exact ⟨x, y, hne, set.dual_Ioo.trans hxy⟩,
  change grade_top α - grade b = grade_top α - grade a + 2 at h,
  linarith [grade_le_grade_top a, grade_le_grade_top b],
end ⟩

end polytope
