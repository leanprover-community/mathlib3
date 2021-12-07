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
def is_simple_order.to_graded_order [decidable_eq α] [preorder α] [bounded_order α] [is_simple_order α] :
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

/-- The nullitope is a polytope. This is the unique graded poset of top grade 0. -/
instance : polytope nullitope :=
{ scon := by apply graded.scon_of_grade_le_two; exact zero_le_two }

/-- The point as a diamond_order. This is the unique graded poset of top grade 1. -/
instance : diamond_order point :=
⟨ by apply diamond_of_grade_le_one; exact le_rfl ⟩

/-- The point as a polytope. This is the unique graded poset of top grade 1. -/
instance : polytope point :=
{ scon := by apply graded.scon_of_grade_le_two; exact one_le_two }

/-- The generic polytope product. -/
def product (α : Type*) [has_le α] [bounded_order α] (β : Type v) [has_le β] [bounded_order β]
(min max : bool) :=
{x : α × β // x = ⊥ ∨ x = ⊤ ∨ (min → (x.fst ≠ ⊥ ∧ x.snd ≠ ⊥)) ∧ (max → (x.fst ≠ ⊤ ∧ x.snd ≠ ⊤))}

namespace product

variables (α : Type*) (β : Type v)

section

variables [has_le α] [bounded_order α] [has_le β] [bounded_order β]

/-- The join of two bounded orders. -/
abbreviation join := product α β ff ff

/-- The direct sum of two bounded orders. -/
abbreviation direct_sum := product α β ff tt

/-- The Cartesian product of two bounded orders. -/
abbreviation cartesian_product := product α β tt ff

/-- The topological product of two bounded orders. -/
abbreviation topological_product := product α β tt tt

notation α ` ⋈ `:50 β:50 := join α β
notation α ` ⊕ `:50 β:50 := direct_sum α β
notation α ` ⊗ `:50 β:50 := cartesian_product α β
notation α ` □ `:50 β:50 := topological_product α β

end

section

variables [preorder α] [bounded_order α] [preorder β] [bounded_order β]

instance {min max : bool} : preorder (product α β min max) :=
{ le := λ a b, a.val ≤ b.val,
  le_refl := λ _, @le_refl (α × β) _ _,
  le_trans := λ _ _ _, @le_trans (α × β) _ _ _ _ }

instance {min max : bool} : order_bot (product α β min max) :=
{ bot := ⟨⊥, or.inl rfl⟩,
  bot_le := λ _, bot_le }

instance {min max : bool} : order_top (product α β min max) :=
{ top := ⟨⊤, or.inr (or.inl rfl)⟩,
  le_top := λ _, le_top }

instance {min max : bool} : inhabited (product α β min max) := ⟨⊥⟩

end

section

variables [partial_order α] [bounded_order α] [partial_order β] [bounded_order β]

lemma foo : (⊥ : α ⋈ β).val = (⊥ : α × β) := refl _

lemma foo' : (⊥ : product α β ff ff).val = (⊥ : α × β) := refl _

instance {min max : bool} : partial_order (product α β min max) :=
{ le_antisymm := λ a b hab hba, subtype.eq (@le_antisymm (α × β) _ a.val b.val hab hba),
  ..(product.preorder α β) }

instance [grade_order α] [graded β] : graded (α ⋈ β) :=
{ grade := λ a, grade a.val.fst + grade a.val.snd,
  grade_bot := sorry,
  strict_mono := sorry,
  hcovers := sorry }

end

end product

end polytope
