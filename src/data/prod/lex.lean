/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import order.synonym

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs of orders, partial orders and linear orders.

## Main declarations

* `prod.lex.<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
-/

variables {α β γ : Type*}

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

lemma le_iff [has_lt α] [has_le β] (a b : α × β) :
  to_lex a ≤ to_lex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := prod.lex_def (<) (≤)

lemma lt_iff [has_lt α] [has_lt β] (a b : α × β) :
  to_lex a < to_lex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 := prod.lex_def (<) (<)

/-- Dictionary / lexicographic preorder for pairs. -/
instance preorder (α β : Type*) [preorder α] [preorder β] : preorder (α ×ₗ β) :=
{ le_refl := by
  { haveI : is_refl β (≤) := ⟨le_refl⟩,
    exact refl_of (prod.lex _ _), },
  le_trans := λ _ _ _, by
  { haveI : is_trans α (<) := ⟨λ _ _ _, lt_trans⟩,
    haveI : is_trans β (≤) := ⟨λ _ _ _, le_trans⟩,
    exact trans_of (prod.lex _ _) },
  lt_iff_le_not_le := λ x₁ x₂, match x₁, x₂ with
  | to_lex (a₁, b₁), to_lex (a₂, b₂) := begin
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
    end
  end,
  .. prod.lex.has_le α β,
  .. prod.lex.has_lt α β }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance partial_order (α β : Type*) [partial_order α] [partial_order β] : partial_order (α ×ₗ β) :=
{ le_antisymm := by
  { haveI : is_strict_order α (<) := { irrefl := lt_irrefl, trans := λ _ _ _, lt_trans },
    haveI : is_antisymm β (≤) := ⟨λ _ _, le_antisymm⟩,
    exact @antisymm _ (prod.lex _ _) _, },
  .. prod.lex.preorder α β }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linear_order (α β : Type*) [linear_order α] [linear_order β] : linear_order (α ×ₗ β) :=
{ le_total := total_of (prod.lex _ _),
  decidable_le := prod.lex.decidable _ _,
  decidable_lt := prod.lex.decidable _ _,
  decidable_eq := lex.decidable_eq _ _,
  .. prod.lex.partial_order α β }

end prod.lex
