/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/
import logic.equiv.basic
import logic.nontrivial
import order.basic

/-!
# Initial lemmas to work with the `order_dual`

## Definitions
`to_dual` and `of_dual` the order reversing identity maps, bundled as equivalences.

## Basic Lemmas to convert between an order and its dual

This file is similar to algebra/group/type_tags.lean
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

namespace order_dual

instance [nontrivial α] : nontrivial αᵒᵈ := by delta order_dual; assumption

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def to_dual : α ≃ αᵒᵈ := ⟨id, id, λ h, rfl, λ h, rfl⟩

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def of_dual : αᵒᵈ ≃ α := to_dual.symm

@[simp] lemma to_dual_symm_eq : (@to_dual α).symm = of_dual := rfl
@[simp] lemma of_dual_symm_eq : (@of_dual α).symm = to_dual := rfl
@[simp] lemma to_dual_of_dual (a : αᵒᵈ) : to_dual (of_dual a) = a := rfl
@[simp] lemma of_dual_to_dual (a : α) : of_dual (to_dual a) = a := rfl

@[simp] lemma to_dual_inj {a b : α} : to_dual a = to_dual b ↔ a = b := iff.rfl
@[simp] lemma of_dual_inj {a b : αᵒᵈ} : of_dual a = of_dual b ↔ a = b := iff.rfl

@[simp] lemma to_dual_le_to_dual [has_le α] {a b : α} : to_dual a ≤ to_dual b ↔ b ≤ a := iff.rfl
@[simp] lemma to_dual_lt_to_dual [has_lt α] {a b : α} : to_dual a < to_dual b ↔ b < a := iff.rfl
@[simp] lemma of_dual_le_of_dual [has_le α] {a b : αᵒᵈ} : of_dual a ≤ of_dual b ↔ b ≤ a := iff.rfl
@[simp] lemma of_dual_lt_of_dual [has_lt α] {a b : αᵒᵈ} : of_dual a < of_dual b ↔ b < a := iff.rfl

lemma le_to_dual [has_le α] {a : αᵒᵈ} {b : α} : a ≤ to_dual b ↔ b ≤ of_dual a := iff.rfl
lemma lt_to_dual [has_lt α] {a : αᵒᵈ} {b : α} : a < to_dual b ↔ b < of_dual a := iff.rfl
lemma to_dual_le [has_le α] {a : α} {b : αᵒᵈ} : to_dual a ≤ b ↔ of_dual b ≤ a := iff.rfl
lemma to_dual_lt [has_lt α] {a : α} {b : αᵒᵈ} : to_dual a < b ↔ of_dual b < a := iff.rfl

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_eliminator]
protected def rec {C : αᵒᵈ → Sort*} (h₂ : Π (a : α), C (to_dual a)) : Π (a : αᵒᵈ), C a := h₂

@[simp] protected lemma «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (to_dual a) := iff.rfl
@[simp] protected lemma «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (to_dual a) := iff.rfl

end order_dual

alias order_dual.to_dual_le_to_dual ↔ _ has_le.le.dual
alias order_dual.to_dual_lt_to_dual ↔ _ has_lt.lt.dual
alias order_dual.of_dual_le_of_dual ↔ _ has_le.le.of_dual
alias order_dual.of_dual_lt_of_dual ↔ _ has_lt.lt.of_dual
