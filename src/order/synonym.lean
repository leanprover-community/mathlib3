/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
import logic.equiv.basic
import logic.nontrivial
import order.basic

/-!
# Type synonyms

This file provides two type synonyms for order theory:
* `order_dual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `prod`, `sigma`, `list`, `finset`.

## Notation

`αᵒᵈ` is notation for `order_dual α`.

The general rule for notation of `lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`lex α`. Instead, explicit
coercions should be inserted:
* `order_dual`: `order_dual.to_dual : α → αᵒᵈ` and `order_dual.of_dual : αᵒᵈ → α`
* `lex`: `to_lex : α → lex α` and `of_lex : lex α → α`.

In fact, those are bundled as `equiv`s to put goals in the right syntactic form for rewriting with
the `equiv` API (`⇑to_lex a` where `⇑` is `coe_fn : (α ≃ lex α) → α → lex α`, instead of a bare
`to_lex a`).

## See also

This file is similar to `algebra.group.type_tags`.
-/

variables {α β γ : Type*}

/-! ### Order dual -/

namespace order_dual

instance [h : nontrivial α] : nontrivial (αᵒᵈ) := h

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def to_dual : α ≃ αᵒᵈ := equiv.refl _

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def of_dual : αᵒᵈ ≃ α := equiv.refl _

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
protected def rec {C : αᵒᵈ → Sort*} (h₂ : Π a : α, C (to_dual a)) : Π a : αᵒᵈ, C a := h₂

@[simp] protected lemma «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (to_dual a) := iff.rfl
@[simp] protected lemma «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (to_dual a) := iff.rfl

alias to_dual_le_to_dual ↔ _ has_le.le.dual
alias to_dual_lt_to_dual ↔ _ has_lt.lt.dual
alias of_dual_le_of_dual ↔ _ has_le.le.of_dual
alias of_dual_lt_of_dual ↔ _ has_lt.lt.of_dual

end order_dual

/-! ### Lexicographic order -/

/-- A type synonym to equip a type with its lexicographic order. -/
def lex (α : Type*) := α

/-- `to_lex` is the identity function to the `lex` of a type.  -/
@[pattern] def to_lex : α ≃ lex α := equiv.refl _

/-- `of_lex` is the identity function from the `lex` of a type.  -/
@[pattern] def of_lex : lex α ≃ α := equiv.refl _

@[simp] lemma to_lex_symm_eq : (@to_lex α).symm = of_lex := rfl
@[simp] lemma of_lex_symm_eq : (@of_lex α).symm = to_lex := rfl
@[simp] lemma to_lex_of_lex (a : lex α) : to_lex (of_lex a) = a := rfl
@[simp] lemma of_lex_to_lex (a : α) : of_lex (to_lex a) = a := rfl
@[simp] lemma to_lex_inj {a b : α} : to_lex a = to_lex b ↔ a = b := iff.rfl
@[simp] lemma of_lex_inj {a b : lex α} :  of_lex a = of_lex b ↔ a = b := iff.rfl

/-- A recursor for `lex`. Use as `induction x using lex.rec`. -/
protected def lex.rec {β : lex α → Sort*} (h : Π a, β (to_lex a)) : Π a, β a := λ a, h (of_lex a)
