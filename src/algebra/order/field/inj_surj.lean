/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.order.field.defs
import algebra.field.basic
import algebra.order.ring.inj_surj

/-!
# Pulling back linearly ordered fields along injective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open function order_dual

variables {ι α β : Type*}

namespace function

/-- Pullback a `linear_ordered_semifield` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def injective.linear_ordered_semifield [linear_ordered_semifield α] [has_zero β] [has_one β]
  [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_inv β] [has_div β]
  [has_pow β ℤ] [has_sup β] [has_inf β] (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
  (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_semifield β :=
{ ..hf.linear_ordered_semiring f zero one add mul nsmul npow nat_cast hsup hinf,
  ..hf.semifield f zero one add mul inv div nsmul npow zpow nat_cast }

/-- Pullback a `linear_ordered_field` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def injective.linear_ordered_field [linear_ordered_field α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_neg β] [has_sub β] [has_pow β ℕ] [has_smul ℕ β] [has_smul ℤ β] [has_smul ℚ β]
  [has_nat_cast β] [has_int_cast β] [has_rat_cast β] [has_inv β] [has_div β] [has_pow β ℤ]
  [has_sup β] [has_inf β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_field β :=
{ .. hf.linear_ordered_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast hsup hinf,
  .. hf.field f zero one add mul neg sub inv div nsmul zsmul qsmul npow zpow nat_cast int_cast
      rat_cast }

end function
