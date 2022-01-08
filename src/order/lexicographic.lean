/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import data.equiv.basic
import data.prod
import tactic.basic

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs and dependent pairs of orders, partial orders
and linear orders.

## Main declarations

* `lex α`: A type synonym of `α` to equip it with its lexicographic order.
* `prod.lex.<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
-/

universes u v

/-- A type synonym to equip a type with its lexicographic order. -/
def lex (α : Type u) := α

variables {α : Type u} {β : Type v} {γ : Type*}

/-- `to_lex` is the identity function to the `lex` of a type.  -/
def to_lex : α ≃ lex α := ⟨id, id, λ h, rfl, λ h, rfl⟩

/-- `of_lex` is the identity function from the `lex` of a type.  -/
def of_lex : lex α ≃ α := to_lex.symm

@[simp] lemma to_lex_symm_eq : (@to_lex α).symm = of_lex := rfl
@[simp] lemma of_lex_symm_eq : (@of_lex α).symm = to_lex := rfl
@[simp] lemma to_lex_of_lex (a : lex α) : to_lex (of_lex a) = a := rfl
@[simp] lemma of_lex_to_lex (a : α) : of_lex (to_lex a) = a := rfl
@[simp] lemma to_lex_inj {a b : α} : to_lex a = to_lex b ↔ a = b := iff.rfl
@[simp] lemma of_lex_inj {a b : lex α} :  of_lex a = of_lex b ↔ a = b := iff.rfl

namespace prod.lex

notation α ` ×ₗ `:35 β:34 := lex (prod α β)

meta instance [has_to_format α] [has_to_format β] : has_to_format (α ×ₗ β) :=
prod.has_to_format

instance decidable_eq (α β : Type*) [decidable_eq α] [decidable_eq β] : decidable_eq (α ×ₗ β) :=
prod.decidable_eq

instance inhabited (α β : Type*) [inhabited α] [inhabited β] : inhabited (α ×ₗ β) :=
prod.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance has_le (α β : Type*) [has_lt α] [has_le β] : has_le (α ×ₗ β) :=
{ le := prod.lex (<) (≤) }

instance has_lt (α β : Type*) [has_lt α] [has_lt β] : has_lt (α ×ₗ β) :=
{ lt := prod.lex (<) (<) }

lemma le_iff [has_lt α] [has_le β] (a b : α ×ₗ β) :
  a ≤ b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := prod.lex_def (<) (≤)

lemma lt_iff [has_lt α] [has_lt β] (a b : α ×ₗ β) :
  a < b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 := prod.lex_def (<) (<)

/-- Dictionary / lexicographic preorder for pairs. -/
instance preorder (α β : Type*) [preorder α] [preorder β] : preorder (α ×ₗ β) :=
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
  .. prod.lex.has_le α β,
  .. prod.lex.has_lt α β }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance partial_order (α β : Type*) [partial_order α] [partial_order β] : partial_order (α ×ₗ β) :=
{ le_antisymm :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩),
    { exfalso, exact lt_irrefl a₁ (lt_trans hlt₁ hlt₂) },
    { exfalso, exact lt_irrefl a₁ hlt₁ },
    { exfalso, exact lt_irrefl a₁ hlt₂ },
    { have := le_antisymm hlt₁ hlt₂, simp [this] }
  end,
  .. prod.lex.preorder α β }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linear_order (α β : Type*) [linear_order α] [linear_order β] : linear_order (α ×ₗ β) :=
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
  .. prod.lex.partial_order α β }

end prod.lex
