/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import data.prod
import logic.equiv.basic
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
@[pattern] def to_lex : α ≃ lex α := ⟨id, id, λ h, rfl, λ h, rfl⟩

/-- `of_lex` is the identity function from the `lex` of a type.  -/
@[pattern] def of_lex : lex α ≃ α := to_lex.symm

@[simp] lemma to_lex_symm_eq : (@to_lex α).symm = of_lex := rfl
@[simp] lemma of_lex_symm_eq : (@of_lex α).symm = to_lex := rfl
@[simp] lemma to_lex_of_lex (a : lex α) : to_lex (of_lex a) = a := rfl
@[simp] lemma of_lex_to_lex (a : α) : of_lex (to_lex a) = a := rfl
@[simp] lemma to_lex_inj {a b : α} : to_lex a = to_lex b ↔ a = b := iff.rfl
@[simp] lemma of_lex_inj {a b : lex α} :  of_lex a = of_lex b ↔ a = b := iff.rfl

/-- A recursor for `lex`. Use as `induction x using lex.rec`. -/
protected def lex.rec {β : lex α → Sort*} (h : Π a, β (to_lex a)) : Π a, β a := λ a, h (of_lex a)

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
