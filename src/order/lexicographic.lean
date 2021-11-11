/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import tactic.basic

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs and dependent pairs of orders, partial orders
and linear orders.

## Main declarations

* `lex α β`: Synonym of `α × β` to equip it with lexicographic order without creating conflicting
  instances.
* `lex_<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `lex α β`
* `dlex_<pre/partial_/linear_>order`: Instances lifting the orders on every `Z a` to the dependent
  pair `Z`.

## See also

The lexicographic ordering on lists is provided in `data.list.basic`.
-/

universes u v

/-- The cartesian product, equipped with the lexicographic order. -/
def lex (α : Type u) (β : Type v) := α × β

variables {α : Type u} {β : Type v}

meta instance [has_to_format α] [has_to_format β] : has_to_format (lex α β) :=
prod.has_to_format

instance [decidable_eq α] [decidable_eq β] : decidable_eq (lex α β) :=
prod.decidable_eq

instance [inhabited α] [inhabited β] : inhabited (lex α β) :=
prod.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance lex_has_le [has_lt α] [has_le β] : has_le (lex α β) :=
{ le := prod.lex (<) (≤) }

instance lex_has_lt [has_lt α] [has_lt β] : has_lt (lex α β) :=
{ lt := prod.lex (<) (<) }

/-- Dictionary / lexicographic preorder for pairs. -/
instance lex_preorder [preorder α] [preorder β] : preorder (lex α β) :=
{ le_refl := λ ⟨l, r⟩, by { right, apply le_refl },
  le_trans :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩,
    { left, apply lt_trans, repeat { assumption } },
    { left, assumption },
    { left, assumption },
    { right, apply le_trans, repeat { assumption } }
  end,
  lt_iff_le_not_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    split,
    { rintros (⟨_, _, _, _, hlt⟩ | ⟨_, _, _, hlt⟩),
     { split,
       { left, assumption },
       { rintro ⟨l,r⟩,
         { apply lt_asymm hlt, assumption },
         { apply lt_irrefl _ hlt } } },
     { split,
       { right, rw lt_iff_le_not_le at hlt, exact hlt.1 },
       { rintro ⟨l,r⟩,
         { apply lt_irrefl a₁, assumption },
         { rw lt_iff_le_not_le at hlt, apply hlt.2, assumption } } } },
    { rintros ⟨⟨h₁ll, h₁lr⟩, h₂r⟩,
      { left, assumption },
      { right, rw lt_iff_le_not_le, split,
        { assumption },
        { intro h, apply h₂r, right, exact h } } }
  end,
  .. lex_has_le,
  .. lex_has_lt }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance lex_partial_order [partial_order α] [partial_order β] : partial_order (lex α β) :=
{ le_antisymm :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩),
    { exfalso, exact lt_irrefl a₁ (lt_trans hlt₁ hlt₂) },
    { exfalso, exact lt_irrefl a₁ hlt₁ },
    { exfalso, exact lt_irrefl a₁ hlt₂ },
    { have := le_antisymm hlt₁ hlt₂, simp [this] }
  end
  .. lex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance lex_linear_order [linear_order α] [linear_order β] : linear_order (lex α β) :=
{ le_total :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    obtain ha | ha := le_total a₁ a₂;
      cases lt_or_eq_of_le ha with a_lt a_eq,
    -- Deal with the two goals with a₁ ≠ a₂
    { left, left, exact a_lt },
    swap,
    { right, left, exact a_lt },
    -- Now deal with the two goals with a₁ = a₂
    all_goals { subst a_eq, obtain hb | hb := le_total b₁ b₂ },
    { left, right, exact hb },
    { right, right, exact hb },
    { left, right, exact hb },
    { right, right, exact hb },
  end,
  decidable_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    obtain a_lt | a_le := linear_order.decidable_le a₁ a₂,
    { -- a₂ < a₁
      left, rw not_le at a_lt, rintro ⟨l, r⟩,
      { apply lt_irrefl a₂, apply lt_trans, repeat { assumption } },
      { apply lt_irrefl a₁, assumption } },
    { -- a₁ ≤ a₂
      by_cases h : a₁ = a₂,
      { rw h,
        obtain b_lt | b_le := linear_order.decidable_le b₁ b₂,
        { -- b₂ < b₁
          left, rw not_le at b_lt, rintro ⟨l, r⟩,
          { apply lt_irrefl a₂, assumption },
          { apply lt_irrefl b₂, apply lt_of_lt_of_le, repeat { assumption } } },
          -- b₁ ≤ b₂
         { right, right, assumption } },
      -- a₁ < a₂
      { right, left, apply lt_of_le_of_ne, repeat { assumption } } }
  end,
  .. lex_partial_order }.

variables {Z : α → Type v}
/--
Dictionary / lexicographic ordering on dependent pairs.

The 'pointwise' partial order `prod.has_le` doesn't make
sense for dependent pairs, so it's safe to mark these as
instances here.
-/
instance dlex_has_le [preorder α] [∀ a, preorder (Z a)] : has_le (Σ' a, Z a) :=
{ le := psigma.lex (<) (λ a, (≤)) }

instance dlex_has_lt [preorder α] [∀ a, preorder (Z a)] : has_lt (Σ' a, Z a) :=
{ lt := psigma.lex (<) (λ a, (<)) }

/-- Dictionary / lexicographic preorder on dependent pairs. -/
instance dlex_preorder [preorder α] [∀ a, preorder (Z a)] : preorder (Σ' a, Z a) :=
{ le_refl := λ ⟨l, r⟩, by { right, apply le_refl },
  le_trans :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩,
    { left, apply lt_trans, repeat { assumption } },
    { left, assumption },
    { left, assumption },
    { right, apply le_trans, repeat { assumption } }
  end,
  lt_iff_le_not_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    split,
    { rintros (⟨_, _, _, _, hlt⟩ | ⟨_, _, _, hlt⟩),
     { split,
       { left, assumption },
       { rintro ⟨l,r⟩,
         { apply lt_asymm hlt, assumption },
         { apply lt_irrefl _ hlt } } },
     { split,
       { right, rw lt_iff_le_not_le at hlt, exact hlt.1 },
       { rintro ⟨l,r⟩,
         { apply lt_irrefl a₁, assumption },
         { rw lt_iff_le_not_le at hlt, apply hlt.2, assumption } } } },
    { rintros ⟨⟨h₁ll, h₁lr⟩, h₂r⟩,
      { left, assumption },
      { right, rw lt_iff_le_not_le, split,
        { assumption },
        { intro h, apply h₂r, right, exact h } } }
  end,
  .. dlex_has_le,
  .. dlex_has_lt }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance dlex_partial_order [partial_order α] [∀ a, partial_order (Z a)] :
  partial_order (Σ' a, Z a) :=
{ le_antisymm :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩),
    { exfalso, exact lt_irrefl a₁ (lt_trans hlt₁ hlt₂) },
    { exfalso, exact lt_irrefl a₁ hlt₁ },
    { exfalso, exact lt_irrefl a₁ hlt₂ },
    { have := le_antisymm hlt₁ hlt₂, simp [this] }
  end
  .. dlex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance dlex_linear_order [linear_order α] [∀ a, linear_order (Z a)] : linear_order (Σ' a, Z a) :=
{ le_total :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    obtain ha | ha := le_total a₁ a₂;
      cases lt_or_eq_of_le ha with a_lt a_eq,
    -- Deal with the two goals with a₁ ≠ a₂
    { left, left, exact a_lt },
    swap,
    { right, left, exact a_lt },
    -- Now deal with the two goals with a₁ = a₂
    all_goals { subst a_eq, obtain hb | hb := le_total b₁ b₂ },
    { left, right, exact hb },
    { right, right, exact hb },
    { left, right, exact hb },
    { right, right, exact hb },
  end,
  decidable_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    obtain a_lt | a_le := linear_order.decidable_le a₁ a₂,
    { -- a₂ < a₁
      left, rw not_le at a_lt, rintro ⟨l, r⟩,
      { apply lt_irrefl a₂, apply lt_trans, repeat { assumption } },
      { apply lt_irrefl a₁, assumption } },
    { -- a₁ ≤ a₂
      by_cases h : a₁ = a₂,
      { subst h,
        obtain b_lt | b_le := linear_order.decidable_le b₁ b₂,
        { -- b₂ < b₁
          left, rw not_le at b_lt, rintro ⟨l, r⟩,
          { apply lt_irrefl a₁, assumption },
          { apply lt_irrefl b₂, apply lt_of_lt_of_le, repeat { assumption } } },
          -- b₁ ≤ b₂
         { right, right, assumption } },
      -- a₁ < a₂
      { right, left, apply lt_of_le_of_ne, repeat { assumption } } }
  end,
  .. dlex_partial_order }.
