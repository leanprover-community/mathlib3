/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.defs
import algebra.order.monoid.basic
import algebra.order.group.instances

/-!
# Pull back ordered groups along injective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}

/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_group
"Pullback an `ordered_add_comm_group` under an injective map."]
def function.injective.ordered_comm_group [ordered_comm_group α] {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β] [has_pow β ℕ] [has_pow β ℤ]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  ordered_comm_group β :=
{ ..partial_order.lift f hf,
  ..hf.ordered_comm_monoid f one mul npow,
  ..hf.comm_group f one mul inv div npow zpow }

/-- Pullback a `linear_ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_add_comm_group
"Pullback a `linear_ordered_add_comm_group` under an injective map."]
def function.injective.linear_ordered_comm_group [linear_ordered_comm_group α] {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β] [has_pow β ℕ] [has_pow β ℤ]
  [has_sup β] [has_inf β] (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_group β :=
{ ..linear_order.lift f hf hsup hinf,
  ..hf.ordered_comm_group f one mul inv div npow zpow }
