/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.ring.defs
import algebra.opposites
import algebra.group_with_zero.inj_surj

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open function

/-!
### `distrib` class
-/

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.distrib {S} [has_mul R] [has_add R] [distrib S]
  (f : R → S) (hf : injective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib R :=
{ mul := (*),
  add := (+),
  left_distrib := λ x y z, hf $ by simp only [*, left_distrib],
  right_distrib := λ x y z, hf $ by simp only [*, right_distrib] }

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib {S} [distrib R] [has_add S] [has_mul S]
  (f : R → S) (hf : surjective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib S :=
{ mul := (*),
  add := (+),
  left_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, left_distrib],
  right_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, right_distrib] }

section injective_surjective_maps

/-!
### Semirings
-/

variables [has_zero β] [has_add β] [has_mul β] [has_smul ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add nsmul, .. hf.distrib f add mul }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.semigroup_with_zero f zero mul }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_mul β] [has_add β]
  [has_smul ℕ β] [has_nat_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  non_assoc_semiring β :=
{ .. hf.add_monoid_with_one f zero one add nsmul nat_cast,
  .. hf.non_unital_non_assoc_semiring f zero add mul nsmul,
  .. hf.mul_one_class f one mul }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.semiring
  {α : Type u} [semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β] [has_pow β ℕ]
  [has_smul ℕ β] [has_nat_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  semiring β :=
{ .. hf.non_assoc_semiring f zero one add mul nsmul nat_cast,
  .. hf.monoid_with_zero f zero one mul npow,
  .. hf.distrib f add mul }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add nsmul, .. hf.distrib f add mul }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.semigroup_with_zero f zero mul }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_smul ℕ β] [has_nat_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  non_assoc_semiring β :=
{ .. hf.add_monoid_with_one f zero one add nsmul nat_cast,
  .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.mul_one_class f one mul }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.semiring
  {α : Type u} [semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β] [has_pow β ℕ]
  [has_smul ℕ β] [has_nat_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  semiring β :=
{ .. hf.non_assoc_semiring f zero one add mul nsmul nat_cast,
  .. hf.monoid_with_zero f zero one mul npow, .. hf.add_comm_monoid f zero add nsmul,
  .. hf.distrib f add mul }

end injective_surjective_maps

section non_unital_comm_semiring
variables [non_unital_comm_semiring α] [non_unital_comm_semiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_comm_semiring [has_zero γ] [has_add γ] [has_mul γ]
  [has_smul ℕ γ] (f : γ → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_comm_semiring γ :=
{ .. hf.non_unital_semiring f zero add mul nsmul, .. hf.comm_semigroup f mul }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_comm_semiring [has_zero γ] [has_add γ] [has_mul γ]
  [has_smul ℕ γ] (f : α → γ) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_comm_semiring γ :=
{ .. hf.non_unital_semiring f zero add mul nsmul, .. hf.comm_semigroup f mul }

end non_unital_comm_semiring

section comm_semiring
variables [comm_semiring α] [comm_semiring β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_semiring
  [has_zero γ] [has_one γ] [has_add γ] [has_mul γ] [has_smul ℕ γ] [has_nat_cast γ]
  [has_pow γ ℕ] (f : γ → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul nsmul npow nat_cast, .. hf.comm_semigroup f mul }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_semiring
  [has_zero γ] [has_one γ] [has_add γ] [has_mul γ] [has_smul ℕ γ] [has_nat_cast γ]
  [has_pow γ ℕ] (f : α → γ) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul nsmul npow nat_cast, .. hf.comm_semigroup f mul }

end comm_semiring

section has_distrib_neg

section has_mul
variables [has_mul α] [has_distrib_neg α]

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.has_distrib_neg [has_neg β] [has_mul β] (f : β → α)
  (hf : injective f) (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) :
  has_distrib_neg β :=
{ neg_mul := λ x y, hf $ by erw [neg, mul, neg, neg_mul, mul],
  mul_neg := λ x y, hf $ by erw [neg, mul, neg, mul_neg, mul],
  ..hf.has_involutive_neg _ neg, ..‹has_mul β› }

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
@[reducible] -- See note [reducible non-instances]
protected def function.surjective.has_distrib_neg [has_neg β] [has_mul β] (f : α → β)
  (hf : surjective f) (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) :
  has_distrib_neg β :=
{ neg_mul := hf.forall₂.2 $ λ x y, by { erw [←neg, ← mul, neg_mul, neg, mul], refl },
  mul_neg := hf.forall₂.2 $ λ x y, by { erw [←neg, ← mul, mul_neg, neg, mul], refl },
  ..hf.has_involutive_neg _ neg, ..‹has_mul β› }

namespace add_opposite

instance : has_distrib_neg αᵃᵒᵖ := unop_injective.has_distrib_neg _ unop_neg unop_mul

end add_opposite

end has_mul

end has_distrib_neg

/-!
### Rings
-/

section non_unital_non_assoc_ring
variables [non_unital_non_assoc_ring α]

/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_non_assoc_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul zsmul, ..hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul }

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_non_assoc_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul zsmul, .. hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul }

end non_unital_non_assoc_ring

section non_unital_ring
variables [non_unital_ring α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, ..hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul, .. hf.semigroup f mul }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, .. hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul, .. hf.semigroup f mul }

end non_unital_ring

section non_assoc_ring
variables [non_assoc_ring α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_assoc_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul,
  .. hf.add_group_with_one f zero one add neg sub nsmul gsmul nat_cast int_cast,
  .. hf.mul_zero_class f zero mul, .. hf.distrib f add mul,
  .. hf.mul_one_class f one mul }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_assoc_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, .. hf.mul_zero_class f zero mul,
  .. hf.add_group_with_one f zero one add neg sub nsmul gsmul nat_cast int_cast,
  .. hf.distrib f add mul, .. hf.mul_one_class f one mul }

end non_assoc_ring

section ring
variables [ring α] {a b c d e : α}

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ring β :=
{ .. hf.add_group_with_one f zero one add neg sub nsmul zsmul nat_cast int_cast,
  .. hf.add_comm_group f zero add neg sub nsmul zsmul,
  .. hf.monoid f one mul npow, .. hf.distrib f add mul }

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ring β :=
{ .. hf.add_group_with_one f zero one add neg sub nsmul zsmul nat_cast int_cast,
  .. hf.add_comm_group f zero add neg sub nsmul zsmul,
  .. hf.monoid f one mul npow, .. hf.distrib f add mul }

end ring

section non_unital_comm_ring
variables [non_unital_comm_ring α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_comm_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_comm_ring β :=
{ .. hf.non_unital_ring f zero add mul neg sub nsmul zsmul, .. hf.comm_semigroup f mul }

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_comm_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_comm_ring β :=
{ .. hf.non_unital_ring f zero add mul neg sub nsmul zsmul, .. hf.comm_semigroup f mul }

end non_unital_comm_ring

section comm_ring
variables [comm_ring α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  .. hf.comm_semigroup f mul }

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  .. hf.comm_semigroup f mul }

end comm_ring
