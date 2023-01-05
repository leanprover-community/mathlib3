/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.with_zero
import algebra.order.monoid.with_top
import algebra.order.monoid.type_tags

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

universe u
variables {α : Type u}

namespace with_zero

local attribute [semireducible] with_zero
variables [has_add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def to_mul_bot : with_zero (multiplicative α) ≃* multiplicative (with_bot α) :=
by exact mul_equiv.refl _

@[simp] lemma to_mul_bot_zero :
  to_mul_bot (0 : with_zero (multiplicative α)) = multiplicative.of_add ⊥ := rfl
@[simp] lemma to_mul_bot_coe (x : multiplicative α) :
  to_mul_bot ↑x = multiplicative.of_add (x.to_add : with_bot α) := rfl
@[simp] lemma to_mul_bot_symm_bot :
  to_mul_bot.symm (multiplicative.of_add (⊥ : with_bot α)) = 0 := rfl
@[simp] lemma to_mul_bot_coe_of_add (x : α) :
  to_mul_bot.symm (multiplicative.of_add (x : with_bot α)) = multiplicative.of_add x := rfl

variables [preorder α] (a b : with_zero (multiplicative α))

lemma to_mul_bot_strict_mono : strict_mono (@to_mul_bot α _) := λ x y, id
@[simp] lemma to_mul_bot_le : to_mul_bot a ≤ to_mul_bot b ↔ a ≤ b := iff.rfl
@[simp] lemma to_mul_bot_lt : to_mul_bot a < to_mul_bot b ↔ a < b := iff.rfl

end with_zero
