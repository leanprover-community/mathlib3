/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/

import algebra.group.defs
import order.synonym

/-!
# Group structure on the order type synonyms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Transfer algebraic instances from `α` to `αᵒᵈ` and `lex α`.
-/

open order_dual

variables {α β : Type*}

/-! ### `order_dual` -/

@[to_additive] instance [h : has_one α] : has_one αᵒᵈ := h
@[to_additive] instance [h : has_mul α] : has_mul αᵒᵈ := h
@[to_additive] instance [h : has_inv α] : has_inv αᵒᵈ := h
@[to_additive] instance [h : has_div α] : has_div αᵒᵈ := h
@[to_additive] instance [h : has_smul α β] : has_smul α βᵒᵈ := h
@[to_additive] instance order_dual.has_smul' [h : has_smul α β] : has_smul αᵒᵈ β := h
@[to_additive order_dual.has_smul]
instance order_dual.has_pow [h : has_pow α β] : has_pow αᵒᵈ β := h
@[to_additive order_dual.has_smul']
instance order_dual.has_pow' [h : has_pow α β] : has_pow α βᵒᵈ := h
@[to_additive] instance [h : semigroup α] : semigroup αᵒᵈ := h
@[to_additive] instance [h : comm_semigroup α] : comm_semigroup αᵒᵈ := h
@[to_additive] instance [h : left_cancel_semigroup α] : left_cancel_semigroup αᵒᵈ := h
@[to_additive] instance [h : right_cancel_semigroup α] : right_cancel_semigroup αᵒᵈ := h
@[to_additive] instance [h : mul_one_class α] : mul_one_class αᵒᵈ := h
@[to_additive] instance [h : monoid α] : monoid αᵒᵈ := h
@[to_additive] instance [h : comm_monoid α] : comm_monoid αᵒᵈ := h
@[to_additive] instance [h : left_cancel_monoid α] : left_cancel_monoid αᵒᵈ := h
@[to_additive] instance [h : right_cancel_monoid α] : right_cancel_monoid αᵒᵈ := h
@[to_additive] instance [h : cancel_monoid α] : cancel_monoid αᵒᵈ := h
@[to_additive] instance [h : cancel_comm_monoid α] : cancel_comm_monoid αᵒᵈ := h
@[to_additive] instance [h : has_involutive_inv α] : has_involutive_inv αᵒᵈ := h
@[to_additive] instance [h : div_inv_monoid α] : div_inv_monoid αᵒᵈ := h
@[to_additive order_dual.subtraction_monoid]
instance [h : division_monoid α] : division_monoid αᵒᵈ := h
@[to_additive order_dual.subtraction_comm_monoid]
instance [h : division_comm_monoid α] : division_comm_monoid αᵒᵈ := h
@[to_additive] instance [h : group α] : group αᵒᵈ := h
@[to_additive] instance [h : comm_group α] : comm_group αᵒᵈ := h

@[simp, to_additive] lemma to_dual_one [has_one α] : to_dual (1 : α) = 1 := rfl
@[simp, to_additive] lemma of_dual_one [has_one α] : (of_dual 1 : α) = 1 := rfl
@[simp, to_additive]
lemma to_dual_mul [has_mul α] (a b : α) : to_dual (a * b) = to_dual a * to_dual b := rfl
@[simp, to_additive]
lemma of_dual_mul [has_mul α] (a b : αᵒᵈ) : of_dual (a * b) = of_dual a * of_dual b := rfl
@[simp, to_additive] lemma to_dual_inv [has_inv α] (a : α) : to_dual a⁻¹ = (to_dual a)⁻¹ := rfl
@[simp, to_additive] lemma of_dual_inv [has_inv α] (a : αᵒᵈ) : of_dual a⁻¹ = (of_dual a)⁻¹ := rfl
@[simp, to_additive]
lemma to_dual_div [has_div α] (a b : α) : to_dual (a / b) = to_dual a / to_dual b := rfl
@[simp, to_additive]
lemma of_dual_div [has_div α] (a b : αᵒᵈ) : of_dual (a / b) = of_dual a / of_dual b := rfl
@[simp, to_additive]
lemma to_dual_smul [has_smul α β] (a : α) (b : β) : to_dual (a • b) = a • to_dual b := rfl
@[simp, to_additive]
lemma of_dual_smul [has_smul α β] (a : α) (b : βᵒᵈ) : of_dual (a • b) = a • of_dual b := rfl
@[simp, to_additive]
lemma to_dual_smul' [has_smul α β] (a : α) (b : β) : to_dual a • b = a • b := rfl
@[simp, to_additive]
lemma of_dual_smul' [has_smul α β] (a : αᵒᵈ) (b : β) : of_dual a • b = a • b := rfl
@[simp, to_additive to_dual_smul, to_additive_reorder 1 4]
lemma to_dual_pow [has_pow α β] (a : α) (b : β) : to_dual (a ^ b) = to_dual a ^ b := rfl
@[simp, to_additive of_dual_smul, to_additive_reorder 1 4]
lemma of_dual_pow [has_pow α β] (a : αᵒᵈ) (b : β) : of_dual (a ^ b) = of_dual a ^ b := rfl
@[simp, to_additive to_dual_smul', to_additive_reorder 1 4]
lemma pow_to_dual [has_pow α β] (a : α) (b : β) : a ^ to_dual b = a ^ b := rfl
@[simp, to_additive of_dual_smul', to_additive_reorder 1 4]
lemma pow_of_dual [has_pow α β] (a : α) (b : βᵒᵈ) : a ^ of_dual b = a ^ b := rfl

/-! ### Lexicographical order -/

@[to_additive] instance [h : has_one α] : has_one (lex α) := h
@[to_additive] instance [h : has_mul α] : has_mul (lex α) := h
@[to_additive] instance [h : has_inv α] : has_inv (lex α) := h
@[to_additive] instance [h : has_div α] : has_div (lex α) := h
@[to_additive] instance [h : has_smul α β] : has_smul α (lex β) := h
@[to_additive] instance lex.has_smul' [h : has_smul α β] : has_smul (lex α) β := h
@[to_additive lex.has_smul] instance lex.has_pow [h : has_pow α β] : has_pow (lex α) β := h
@[to_additive lex.has_smul'] instance lex.has_pow' [h : has_pow α β] : has_pow α (lex β) := h
@[to_additive] instance [h : semigroup α] : semigroup (lex α) := h
@[to_additive] instance [h : comm_semigroup α] : comm_semigroup (lex α) := h
@[to_additive] instance [h : left_cancel_semigroup α] : left_cancel_semigroup (lex α) := h
@[to_additive] instance [h : right_cancel_semigroup α] : right_cancel_semigroup (lex α) := h
@[to_additive] instance [h : mul_one_class α] : mul_one_class (lex α) := h
@[to_additive] instance [h : monoid α] : monoid (lex α) := h
@[to_additive] instance [h : comm_monoid α] : comm_monoid (lex α) := h
@[to_additive] instance [h : left_cancel_monoid α] : left_cancel_monoid (lex α) := h
@[to_additive] instance [h : right_cancel_monoid α] : right_cancel_monoid (lex α) := h
@[to_additive] instance [h : cancel_monoid α] : cancel_monoid (lex α) := h
@[to_additive] instance [h : cancel_comm_monoid α] : cancel_comm_monoid (lex α) := h
@[to_additive] instance [h : has_involutive_inv α] : has_involutive_inv (lex α) := h
@[to_additive] instance [h : div_inv_monoid α] : div_inv_monoid (lex α) := h
@[to_additive order_dual.subtraction_monoid]
instance [h : division_monoid α] : division_monoid (lex α) := h
@[to_additive order_dual.subtraction_comm_monoid]
instance [h : division_comm_monoid α] : division_comm_monoid (lex α) := h
@[to_additive] instance [h : group α] : group (lex α) := h
@[to_additive] instance [h : comm_group α] : comm_group (lex α) := h

@[simp, to_additive] lemma to_lex_one [has_one α] : to_lex (1 : α) = 1 := rfl
@[simp, to_additive] lemma of_lex_one [has_one α] : (of_lex 1 : α) = 1 := rfl
@[simp, to_additive]
lemma to_lex_mul [has_mul α] (a b : α) : to_lex (a * b) = to_lex a * to_lex b := rfl
@[simp, to_additive]
lemma of_lex_mul [has_mul α] (a b : lex α) : of_lex (a * b) = of_lex a * of_lex b := rfl
@[simp, to_additive] lemma to_lex_inv [has_inv α] (a : α) : to_lex a⁻¹ = (to_lex a)⁻¹ := rfl
@[simp, to_additive] lemma of_lex_inv [has_inv α] (a : lex α) : of_lex a⁻¹ = (of_lex a)⁻¹ := rfl
@[simp, to_additive]
lemma to_lex_div [has_div α] (a b : α) : to_lex (a / b) = to_lex a / to_lex b := rfl
@[simp, to_additive]
lemma of_lex_div [has_div α] (a b : lex α) : of_lex (a / b) = of_lex a / of_lex b := rfl
@[simp, to_additive]
lemma to_lex_smul [has_smul α β] (a : α) (b : β) : to_lex (a • b) = a • to_lex b := rfl
@[simp, to_additive]
lemma of_lex_smul [has_smul α β] (a : α) (b : lex β) : of_lex (a • b) = a • of_lex b := rfl
@[simp, to_additive]
lemma to_lex_smul' [has_smul α β] (a : α) (b : β) : to_lex a • b = a • b := rfl
@[simp, to_additive]
lemma of_lex_smul' [has_smul α β] (a : lex α) (b : β) : of_lex a • b = a • b := rfl
@[simp, to_additive to_lex_smul, to_additive_reorder 1 4]
lemma to_lex_pow [has_pow α β] (a : α) (b : β) : to_lex (a ^ b) = to_lex a ^ b := rfl
@[simp, to_additive of_lex_smul, to_additive_reorder 1 4]
lemma of_lex_pow [has_pow α β] (a : lex α) (b : β) : of_lex (a ^ b) = of_lex a ^ b := rfl
@[simp, to_additive to_lex_smul, to_additive_reorder 1 4]
lemma pow_to_lex [has_pow α β] (a : α) (b : β) : a ^ to_lex b = a ^ b := rfl
@[simp, to_additive of_lex_smul, to_additive_reorder 1 4]
lemma pow_of_lex [has_pow α β] (a : α) (b : lex β) : a ^ of_lex b = a ^ b := rfl
