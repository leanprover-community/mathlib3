/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.order.ring.defs
import algebra.order.monoid.cancel.basic
import algebra.ring.inj_surj

/-!
# Pulling back ordered rings along injective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open function

universe u
variables {α : Type u} {β : Type*}

namespace function.injective

/-- Pullback an `ordered_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def ordered_semiring [ordered_semiring α] [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  ordered_semiring β :=
{ zero_le_one := show f 0 ≤ f 1, by simp only [zero, one, zero_le_one],
  mul_le_mul_of_nonneg_left := λ a b c h hc, show f (c * a) ≤ f (c * b),
    by { rw [mul, mul], refine mul_le_mul_of_nonneg_left h _, rwa ←zero },
  mul_le_mul_of_nonneg_right := λ a b c h hc, show f (a * c) ≤ f (b * c),
    by { rw [mul, mul], refine mul_le_mul_of_nonneg_right h _, rwa ←zero },
  ..hf.ordered_add_comm_monoid f zero add nsmul,
  ..hf.semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback an `ordered_comm_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def ordered_comm_semiring [ordered_comm_semiring α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] (f : β → α) (hf : injective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
  ordered_comm_semiring β :=
{ ..hf.comm_semiring f zero one add mul nsmul npow nat_cast,
  ..hf.ordered_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback an `ordered_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def ordered_ring [ordered_ring α] [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β]
  [has_int_cast β] (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ordered_ring β :=
{ mul_nonneg := λ a b ha hb, show f 0 ≤ f (a * b),
    by { rw [zero, mul], apply mul_nonneg; rwa ← zero },
  ..hf.ordered_semiring f zero one add mul nsmul npow nat_cast,
  ..hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback an `ordered_comm_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def ordered_comm_ring [ordered_comm_ring α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_neg β] [has_sub β] [has_pow β ℕ] [has_smul ℕ β] [has_smul ℤ β] [has_nat_cast β]
  [has_int_cast β] (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ordered_comm_ring β :=
{ ..hf.ordered_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  ..hf.comm_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `strict_ordered_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def strict_ordered_semiring [strict_ordered_semiring α] [has_zero β] [has_one β]
  [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] (f : β → α)
  (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
  strict_ordered_semiring β :=
{ mul_lt_mul_of_pos_left := λ a b c h hc, show f (c * a) < f (c * b),
    by simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa ←zero),
  mul_lt_mul_of_pos_right := λ a b c h hc, show f (a * c) < f (b * c),
    by simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa ←zero),
  ..hf.ordered_cancel_add_comm_monoid f zero add nsmul,
  ..hf.ordered_semiring f zero one add mul nsmul npow nat_cast,
  ..pullback_nonzero f zero one }

/-- Pullback a `strict_ordered_comm_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def strict_ordered_comm_semiring [strict_ordered_comm_semiring α] [has_zero β] [has_one β]
  [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] (f : β → α)
  (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
  strict_ordered_comm_semiring β :=
{ ..hf.comm_semiring f zero one add mul nsmul npow nat_cast,
  ..hf.strict_ordered_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `strict_ordered_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def strict_ordered_ring [strict_ordered_ring α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β]
  [has_int_cast β] (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  strict_ordered_ring β :=
{ mul_pos := λ a b a0 b0, show f 0 < f (a * b), by { rw [zero, mul], apply mul_pos; rwa ← zero },
  ..hf.strict_ordered_semiring f zero one add mul nsmul npow nat_cast,
  ..hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `strict_ordered_comm_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def strict_ordered_comm_ring [strict_ordered_comm_ring α] [has_zero β]
  [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_pow β ℕ] [has_smul ℕ β]
  [has_smul ℤ β] [has_nat_cast β] [has_int_cast β] (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  strict_ordered_comm_ring β :=
{ ..hf.strict_ordered_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  ..hf.comm_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `linear_ordered_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def linear_ordered_semiring [linear_ordered_semiring α] [has_zero β] [has_one β]
  [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_sup β] [has_inf β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
  (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_semiring β :=
{ .. linear_order.lift f hf hsup hinf,
  .. hf.strict_ordered_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `linear_ordered_semiring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def linear_ordered_comm_semiring [linear_ordered_comm_semiring α]
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β]
  [has_sup β] [has_inf β] (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
  (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_semiring β :=
{ ..hf.linear_ordered_semiring f zero one add mul nsmul npow nat_cast hsup hinf,
  ..hf.strict_ordered_comm_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `linear_ordered_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def linear_ordered_ring [linear_ordered_ring α] [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β]
  [has_int_cast β] [has_sup β] [has_inf β] (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_ring β :=
{ .. linear_order.lift f hf hsup hinf,
  .. hf.strict_ordered_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `linear_ordered_comm_ring` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
protected def linear_ordered_comm_ring [linear_ordered_comm_ring α] [has_zero β]
  [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_pow β ℕ] [has_smul ℕ β]
  [has_smul ℤ β] [has_nat_cast β] [has_int_cast β]  [has_sup β] [has_inf β] (f : β → α)
  (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
  (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_ring β :=
{ .. linear_order.lift f hf hsup hinf,
  .. hf.strict_ordered_comm_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

end function.injective
