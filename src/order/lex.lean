/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import logic.equiv.basic

/-!
# Lexicographic order

This file defines `lex α`, a type synonym of `α` to equip it with its lexicographic order. Examples
of types which admit a lexicographic order include `prod`, `sigma`, `list`, `finset`.

The general rule for notation of such types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `lex α`. Instead, explicit coercions
should be inserted using `to_lex : α → lex α` and `of_lex : lex α → α`. In fact, `to_lex` and
`of_lex` are bundled as `equiv`s to put goals in the right syntactic form for rewriting with the
`equiv` API (`⇑to_lex a` where `⇑` is `coe_fn : (α ≃ lex α) → α → lex α`, instead of `to_lex a`).

## See also

This file is similar to `algebra.group.type_tags` and `order.order_dual`.
-/

/-- A type synonym to equip a type with its lexicographic order. -/
def lex (α : Type*) := α

variables {α β γ : Type*}

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
