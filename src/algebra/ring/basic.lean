/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.ring.defs
import algebra.regular.basic
import algebra.hom.group
import algebra.opposites

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.degs`.

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

/-!
### Semirings
-/

section injective_surjective_maps

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

namespace add_hom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_left {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨(*) r, mul_add r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_right {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨λ a, a * r, λ _ _, add_mul _ _ r⟩

end add_hom

section add_hom_class

variables {F : Type*} [non_assoc_semiring α] [non_assoc_semiring β] [add_hom_class F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp] lemma map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
map_add _ _ _

end add_hom_class

namespace add_monoid_hom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := (*) r,
  map_zero' := mul_zero r,
  map_add' := mul_add r }

@[simp] lemma coe_mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_left r) = (*) r := rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := λ a, a * r,
  map_zero' := zero_mul r,
  map_add' := λ _ _, add_mul _ _ r }

@[simp] lemma coe_mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_right r) = (* r) := rfl

lemma mul_right_apply {R : Type*} [non_unital_non_assoc_semiring R] (a r : R) :
  mul_right r a = a * r := rfl

end add_monoid_hom

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

open mul_opposite

instance : has_distrib_neg αᵐᵒᵖ :=
{ neg_mul := λ _ _, unop_injective $ mul_neg _ _,
  mul_neg := λ _ _, unop_injective $ neg_mul _ _,
  ..mul_opposite.has_involutive_neg _ }

end has_mul

section group
variables [group α] [has_distrib_neg α]

@[simp] lemma inv_neg' (a : α) : (- a)⁻¹ = - a⁻¹ :=
by rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg,neg_neg, mul_left_inv]

end group

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

@[priority 100]
instance non_unital_non_assoc_ring.to_has_distrib_neg : has_distrib_neg α :=
{ neg := has_neg.neg,
  neg_neg := neg_neg,
  neg_mul := λ a b, eq_neg_of_add_eq_zero_left $ by rw [←right_distrib, add_left_neg, zero_mul],
  mul_neg := λ a b, eq_neg_of_add_eq_zero_left $ by rw [←left_distrib, add_left_neg, mul_zero] }

lemma mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub_left_distrib ← mul_sub

lemma mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias mul_sub_right_distrib ← sub_mul

variables {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp [add_comm]
    ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin rw h, simp end) (λ h,
                                                  begin rw ← h, simp end)
    ... ↔ (a - b) * e + c = d   : begin simp [sub_mul, sub_add_eq_add_sub] end

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
assume h,
calc
  (a - b) * e + c = (a * e + c) - b * e : begin simp [sub_mul, sub_add_eq_add_sub] end
              ... = d                   : begin rw h, simp [@add_sub_cancel α] end

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

lemma sub_one_mul (a b : α) : (a - 1) * b = a * b - b :=
by rw [sub_mul, one_mul]
lemma mul_sub_one (a b : α) : a * (b - 1) = a * b - a :=
by rw [mul_sub, mul_one]
lemma one_sub_mul (a b : α) : (1 - a) * b = b - a * b :=
by rw [sub_mul, one_mul]
lemma mul_one_sub (a b : α) : a * (1 - b) = a - a * b :=
by rw [mul_sub, mul_one]

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

namespace units

section has_distrib_neg
variables [monoid α] [has_distrib_neg α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg αˣ := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast] protected theorem coe_neg (u : αˣ) : (↑-u : α) = -u := rfl

@[simp, norm_cast] protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 := rfl

instance : has_distrib_neg αˣ := units.ext.has_distrib_neg _ units.coe_neg units.coe_mul

@[field_simps] lemma neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = (-a) /ₚ u :=
by simp only [divp, neg_mul]

end has_distrib_neg

section ring

variables [ring α] {a b : α}

@[field_simps] lemma divp_add_divp_same (a b : α) (u : αˣ) :
  a /ₚ u + b /ₚ u = (a + b) /ₚ u :=
by simp only [divp, add_mul]

@[field_simps] lemma divp_sub_divp_same (a b : α) (u : αˣ) :
  a /ₚ u - b /ₚ u = (a - b) /ₚ u :=
by rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]

@[field_simps] lemma add_divp (a b : α) (u : αˣ)  : a + b /ₚ u = (a * u + b) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u :=
by simp only [divp, sub_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u :=
begin
  simp only [divp, sub_mul, sub_right_inj],
  assoc_rw [units.mul_inv, mul_one],
end

end ring

end units

lemma is_unit.neg [monoid α] [has_distrib_neg α] {a : α} : is_unit a → is_unit (-a)
| ⟨x, hx⟩ := hx ▸ (-x).is_unit

@[simp]
lemma is_unit.neg_iff [monoid α] [has_distrib_neg α] (a : α) : is_unit (-a) ↔ is_unit a :=
⟨λ h, neg_neg a ▸ h.neg, is_unit.neg⟩

lemma is_unit.sub_iff [ring α] {x y : α} :
  is_unit (x - y) ↔ is_unit (y - x) :=
(is_unit.neg_iff _).symm.trans $ neg_sub x y ▸ iff.rfl

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

local attribute [simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm]),
  refine ⟨b - x, _, by simp, by rw this⟩,
  rw [this, sub_add, ← sub_mul, sub_self]
end

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

lemma succ_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a + 1 ≠ a :=
λ h, one_ne_zero ((add_right_inj a).mp (by simp [h]))

lemma pred_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a - 1 ≠ a :=
λ h, one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))

namespace semiconj_by

@[simp] lemma add_right [distrib R] {a x y x' y' : R}
  (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x + x') (y + y') :=
by simp only [semiconj_by, left_distrib, right_distrib, h.eq, h'.eq]

@[simp] lemma add_left [distrib R] {a b x y : R}
  (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a + b) x y :=
by simp only [semiconj_by, left_distrib, right_distrib, ha.eq, hb.eq]

section
variables [has_mul R] [has_distrib_neg R] {a x y : R}

lemma neg_right (h : semiconj_by a x y) : semiconj_by a (-x) (-y) :=
by simp only [semiconj_by, h.eq, neg_mul, mul_neg]

@[simp] lemma neg_right_iff : semiconj_by a (-x) (-y) ↔ semiconj_by a x y :=
⟨λ h, neg_neg x ▸ neg_neg y ▸ h.neg_right, semiconj_by.neg_right⟩

lemma neg_left (h : semiconj_by a x y) : semiconj_by (-a) x y :=
by simp only [semiconj_by, h.eq, neg_mul, mul_neg]

@[simp] lemma neg_left_iff : semiconj_by (-a) x y ↔ semiconj_by a x y :=
⟨λ h, neg_neg a ▸ h.neg_left, semiconj_by.neg_left⟩

end

section
variables [mul_one_class R] [has_distrib_neg R] {a x y : R}

@[simp] lemma neg_one_right (a : R) : semiconj_by a (-1) (-1) :=
(one_right a).neg_right

@[simp] lemma neg_one_left (x : R) : semiconj_by (-1) x x :=
(semiconj_by.one_left x).neg_left

end

section
variables [non_unital_non_assoc_ring R] {a b x y x' y' : R}

@[simp] lemma sub_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x - x') (y - y') :=
by simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp] lemma sub_left (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a - b) x y :=
by simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end

end semiconj_by

namespace commute

@[simp] theorem add_right [distrib R] {a b c : R} :
  commute a b → commute a c → commute a (b + c) :=
semiconj_by.add_right

@[simp] theorem add_left [distrib R] {a b c : R} :
  commute a c → commute b c → commute (a + b) c :=
semiconj_by.add_left

lemma bit0_right [distrib R] {x y : R} (h : commute x y) : commute x (bit0 y) :=
h.add_right h

lemma bit0_left [distrib R] {x y : R} (h : commute x y) : commute (bit0 x) y :=
h.add_left h

lemma bit1_right [non_assoc_semiring R] {x y : R} (h : commute x y) : commute x (bit1 y) :=
h.bit0_right.add_right (commute.one_right x)

lemma bit1_left [non_assoc_semiring R] {x y : R} (h : commute x y) : commute (bit1 x) y :=
h.bit0_left.add_left (commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
lemma mul_self_sub_mul_self_eq [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a + b) * (a - b) :=
by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

lemma mul_self_sub_mul_self_eq' [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a - b) * (a + b) :=
by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

lemma mul_self_eq_mul_self_iff [non_unital_non_assoc_ring R] [no_zero_divisors R] {a b : R}
  (h : commute a b) : a * a = b * b ↔ a = b ∨ a = -b :=
by rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
  add_eq_zero_iff_eq_neg]

section
variables [has_mul R] [has_distrib_neg R] {a b : R}

theorem neg_right : commute a b → commute a (- b) := semiconj_by.neg_right
@[simp] theorem neg_right_iff : commute a (-b) ↔ commute a b := semiconj_by.neg_right_iff

theorem neg_left : commute a b → commute (- a) b := semiconj_by.neg_left
@[simp] theorem neg_left_iff : commute (-a) b ↔ commute a b := semiconj_by.neg_left_iff

end

section
variables [mul_one_class R] [has_distrib_neg R] {a : R}

@[simp] theorem neg_one_right (a : R) : commute a (-1) := semiconj_by.neg_one_right a
@[simp] theorem neg_one_left (a : R): commute (-1) a := semiconj_by.neg_one_left a

end

section
variables [non_unital_non_assoc_ring R] {a b c : R}

@[simp] theorem sub_right : commute a b → commute a c → commute a (b - c) := semiconj_by.sub_right
@[simp] theorem sub_left : commute a c → commute b c → commute (a - b) c := semiconj_by.sub_left

end

end commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [comm_ring R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
(commute.all a b).mul_self_sub_mul_self_eq

lemma mul_self_sub_one [non_assoc_ring R] (a : R) : a * a - 1 = (a + 1) * (a - 1) :=
by rw [←(commute.one_right a).mul_self_sub_mul_self_eq, mul_one]

lemma mul_self_eq_mul_self_iff [comm_ring R] [no_zero_divisors R] {a b : R} :
  a * a = b * b ↔ a = b ∨ a = -b :=
(commute.all a b).mul_self_eq_mul_self_iff

lemma mul_self_eq_one_iff [non_assoc_ring R] [no_zero_divisors R] {a : R} :
  a * a = 1 ↔ a = 1 ∨ a = -1 :=
by rw [←(commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

namespace units

@[field_simps] lemma divp_add_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) :=
begin
  simp only [divp, add_mul, mul_inv_rev, coe_mul],
  rw [mul_comm (↑u₁ * b), mul_comm b],
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one],
end

@[field_simps] lemma divp_sub_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
  (a /ₚ u₁) - (b /ₚ u₂) = ((a * u₂) - (u₁ * b)) /ₚ (u₁ * u₂) :=
by simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
lemma inv_eq_self_iff [ring R] [no_zero_divisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
begin
  rw inv_eq_iff_mul_eq_one,
  simp only [ext_iff],
  push_cast,
  exact mul_self_eq_one_iff
end

end units

/-! ### Order dual -/

instance [h : distrib α] : distrib αᵒᵈ := h
instance [has_mul α] [has_add α] [h : left_distrib_class α] : left_distrib_class αᵒᵈ := h
instance [has_mul α] [has_add α] [h : right_distrib_class α] : right_distrib_class αᵒᵈ := h
instance [h : non_unital_non_assoc_semiring α] : non_unital_non_assoc_semiring αᵒᵈ := h
instance [h : non_unital_semiring α] : non_unital_semiring αᵒᵈ := h
instance [h : non_assoc_semiring α] : non_assoc_semiring αᵒᵈ := h
instance [h : semiring α] : semiring αᵒᵈ := h
instance [h : non_unital_comm_semiring α] : non_unital_comm_semiring αᵒᵈ := h
instance [h : comm_semiring α] : comm_semiring αᵒᵈ := h
instance [has_mul α] [h : has_distrib_neg α] : has_distrib_neg αᵒᵈ := h
instance [h : non_unital_non_assoc_ring α] : non_unital_non_assoc_ring αᵒᵈ := h
instance [h : non_unital_ring α] : non_unital_ring αᵒᵈ := h
instance [h : non_assoc_ring α] : non_assoc_ring αᵒᵈ := h
instance [h : ring α] : ring αᵒᵈ := h
instance [h : non_unital_comm_ring α] : non_unital_comm_ring αᵒᵈ := h
instance [h : comm_ring α] : comm_ring αᵒᵈ := h
instance [ring α] [h : is_domain α] : is_domain αᵒᵈ := h

/-! ### Lexicographical order -/

instance [h : distrib α] : distrib (lex α) := h
instance [has_mul α] [has_add α] [h : left_distrib_class α] : left_distrib_class (lex α) := h
instance [has_mul α] [has_add α] [h : right_distrib_class α] : right_distrib_class (lex α) := h
instance [h : non_unital_non_assoc_semiring α] : non_unital_non_assoc_semiring (lex α) := h
instance [h : non_unital_semiring α] : non_unital_semiring (lex α) := h
instance [h : non_assoc_semiring α] : non_assoc_semiring (lex α) := h
instance [h : semiring α] : semiring (lex α) := h
instance [h : non_unital_comm_semiring α] : non_unital_comm_semiring (lex α) := h
instance [h : comm_semiring α] : comm_semiring (lex α) := h
instance [has_mul α] [h : has_distrib_neg α] : has_distrib_neg (lex α) := h
instance [h : non_unital_non_assoc_ring α] : non_unital_non_assoc_ring (lex α) := h
instance [h : non_unital_ring α] : non_unital_ring (lex α) := h
instance [h : non_assoc_ring α] : non_assoc_ring (lex α) := h
instance [h : ring α] : ring (lex α) := h
instance [h : non_unital_comm_ring α] : non_unital_comm_ring (lex α) := h
instance [h : comm_ring α] : comm_ring (lex α) := h
instance [ring α] [h : is_domain α] : is_domain (lex α) := h
