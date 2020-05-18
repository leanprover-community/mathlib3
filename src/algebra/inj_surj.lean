/-
Copyright (c) 2014 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.ring

/-!
# Lifting algebraic data classes along injective/surjective maps

This file provides definitions that are meant to deal with
situations such as the following:

Suppose that `G` is a group, and `H` is a type endowed with
`has_one H`, `has_mul H`, and `has_inv H`.
Suppose furthermore, that `f : G → H` is a surjective map
that respects the multiplication, and the unit elements.
Then `H` satisfies the group axioms.

The relevant definition in this case is `group_of_surjective`.
Dually, there is also `group_of_injective`.
And there are versions for (additive) (commutative) semigroups/monoids,
and for (commutative) (semi)rings.
-/

section
open function
variables {M₁ : Type*} {M₂ : Type*} [has_mul M₁]

/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup. -/
@[to_additive add_semigroup_of_injective
"A type endowed with `+` is an additive semigroup,
if it admits an injective map that preserves `+` to an additive semigroup."]
def semigroup_of_injective [semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup M₁ :=
{ mul_assoc := λ x y z, hf $ by erw [mul, mul, mul, mul, mul_assoc],
  ..‹has_mul M₁› }

/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup. -/
@[to_additive add_comm_semigroup_of_injective
"A type endowed with `+` is an additive commutative semigroup,
if it admits an injective map that preserves `+` to an additive commutative semigroup."]
def comm_semigroup_of_injective [comm_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semigroup M₁ :=
{ mul_comm := λ x y, hf $ by erw [mul, mul, mul_comm],
  ..semigroup_of_injective f hf mul }

end

section
open function
variables {M₁ : Type*} {M₂ : Type*} [has_mul M₂]

/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup. -/
@[to_additive add_semigroup_of_surjective
"A type endowed with `+` is an additive semigroup,
if it admits a surjective map that preserves `+` from an additive semigroup."]
def semigroup_of_surjective [semigroup M₁] (f : M₁ → M₂) (hf : surjective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup M₂ :=
{ mul_assoc := λ x y z,
  begin
    rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩, rcases hf z with ⟨z, rfl⟩,
    erw [← mul, ←  mul, ← mul, ← mul, mul_assoc]
  end,
  ..‹has_mul M₂› }

/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup. -/
@[to_additive add_comm_semigroup_of_surjective
"A type endowed with `+` is an additive commutative semigroup,
if it admits a surjective map that preserves `+` from an additive commutative semigroup."]
def comm_semigroup_of_surjective [comm_semigroup M₁] (f : M₁ → M₂) (hf : surjective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semigroup M₂ :=
{ mul_comm := λ x y,
  begin
    rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    erw [← mul, ←  mul, mul_comm]
  end,
  ..semigroup_of_surjective f hf mul }

end

section
open function
variables {M₁ : Type*} {M₂ : Type*} [has_one M₁] [has_mul M₁]

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid. -/
@[to_additive add_monoid_of_injective
"A type endowed with `0` and `+` is an additive monoid,
if it admits an injective map that preserves `0` and `+` to an additive monoid."]
def monoid_of_injective [monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid M₁ :=
{ one_mul := λ x, hf $ by erw [mul, one, one_mul],
  mul_one := λ x, hf $ by erw [mul, one, mul_one],
  ..semigroup_of_injective f hf mul, ..‹has_one M₁› }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid. -/
@[to_additive add_comm_monoid_of_injective
"A type endowed with `0` and `+` is an additive commutative monoid,
if it admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
def comm_monoid_of_injective [comm_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid M₁ :=
{ ..comm_semigroup_of_injective f hf mul, ..monoid_of_injective f hf one mul }

variables [has_inv M₁]

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group. -/
@[to_additive add_group_of_injective
"A type endowed with `0` and `+` is an additive group,
if it admits an injective map that preserves `0` and `+` to an additive group."]
def group_of_injective [group M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) :
  group M₁ :=
{ mul_left_inv := λ x, hf $ by erw [mul, inv, mul_left_inv, one],
  ..monoid_of_injective f hf one mul, ..‹has_inv M₁› }

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group. -/
@[to_additive add_comm_group_of_injective
"A type endowed with `0` and `+` is an additive commutative group,
if it admits an injective map that preserves `0` and `+` to an additive commutative group."]
def comm_group_of_injective [comm_group M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) :
  comm_group M₁ :=
{ ..comm_monoid_of_injective f hf one mul, ..group_of_injective f hf one mul inv }

end

section
open function
variables {M₁ : Type*} {M₂ : Type*} [has_one M₂] [has_mul M₂]

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` from a monoid. -/
@[to_additive add_monoid_of_surjective
"A type endowed with `0` and `+` is an additive monoid,
if it admits a surjective map that preserves `0` and `+` to an additive monoid."]
def monoid_of_surjective [monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid M₂ :=
{ one_mul := λ x, by { rcases hf x with ⟨x, rfl⟩, show 1 * f x = f x, erw [← one, ← mul, one_mul] },
  mul_one := λ x, by { rcases hf x with ⟨x, rfl⟩, erw [← one, ← mul, mul_one] },
  ..‹has_one M₂›, ..semigroup_of_surjective f hf mul }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid. -/
@[to_additive add_comm_monoid_of_surjective
"A type endowed with `0` and `+` is an additive commutative monoid,
if it admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
def comm_monoid_of_surjective [comm_monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid M₂ :=
{ ..comm_semigroup_of_surjective f hf mul, ..monoid_of_surjective f hf one mul }

variables [has_inv M₂]

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` from a group. -/
@[to_additive add_group_of_surjective
"A type endowed with `0` and `+` is an additive group,
if it admits a surjective map that preserves `0` and `+` to an additive group."]
def group_of_surjective [group M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) :
  group M₂ :=
{ mul_left_inv := λ x, by { rcases hf x with ⟨x, rfl⟩, erw [← one, ← mul_left_inv x, mul, inv], refl },
  ..‹has_inv M₂›, ..monoid_of_surjective f hf one mul }

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` from a commutative group. -/
@[to_additive add_comm_group_of_surjective
"A type endowed with `0` and `+` is an additive commutative group,
if it admits a surjective map that preserves `0` and `+` to an additive commutative group."]
def comm_group_of_surjective [comm_group M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) :
  comm_group M₂ :=
{ ..comm_monoid_of_surjective f hf one mul, ..group_of_surjective f hf one mul inv }

end

section
open function
variables {R₁ : Type*} {R₂ : Type*} [has_zero R₁] [has_one R₁] [has_add R₁] [has_mul R₁]

/-- A type endowed with `0`, `1`, `+` and `*` is a semiring,
if it admits an injective map that preserves `0`, `1`, `+` and `*` to a semiring. -/
def semiring_of_injective [semiring R₂] (f : R₁ → R₂) (hf : injective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  semiring R₁ :=
{ left_distrib  := λ x y z, hf $ by erw [mul, add, add, mul, mul, left_distrib],
  right_distrib := λ x y z, hf $ by erw [mul, add, add, mul, mul, right_distrib],
  zero_mul      := λ x, hf $ by erw [mul, zero, zero_mul],
  mul_zero      := λ x, hf $ by erw [mul, zero, mul_zero],
  ..add_comm_monoid_of_injective f hf zero add, ..monoid_of_injective f hf one mul }

/-- A type endowed with `0`, `1`, `+` and `*` is a commutative semiring,
if it admits an injective map that preserves `0`, `1`, `+` and `*` to a commutative semiring. -/
def comm_semiring_of_injective [comm_semiring R₂] (f : R₁ → R₂) (hf : injective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semiring R₁ :=
{ ..comm_monoid_of_injective f hf one mul, ..semiring_of_injective f hf zero one add mul }

variables [has_neg R₁]

/-- A type endowed with `0`, `1`, `+`, `*` and `-` is a ring,
if it admits an injective map that preserves `0`, `1`, `+`, `*` and `-` to a ring. -/
def ring_of_injective [ring R₂] (f : R₁ → R₂) (hf : injective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) :
  ring R₁ :=
{ ..add_comm_group_of_injective f hf zero add neg, ..semiring_of_injective f hf zero one add mul }

/-- A type endowed with `0`, `1`, `+`, `*` and `-` is a commutative ring,
if it admits an injective map that preserves `0`, `1`, `+`, `*` and `-` to a commutative ring. -/
def comm_ring_of_injective [comm_ring R₂] (f : R₁ → R₂) (hf : injective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) :
  comm_ring R₁ :=
{ ..comm_monoid_of_injective f hf one mul, ..ring_of_injective f hf zero one add mul neg }

end

section
open function
variables {R₁ : Type*} {R₂ : Type*} [has_zero R₂] [has_one R₂] [has_add R₂] [has_mul R₂]

/-- A type endowed with `0`, `1`, `+` and `*` is a semiring,
if it admits a surjective map that preserves `0`, `1`, `+` and `*` from a semiring. -/
def semiring_of_surjective [semiring R₁] (f : R₁ → R₂) (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  semiring R₂ :=
{ left_distrib  := λ x y z,
  begin
    rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩, rcases hf z with ⟨z, rfl⟩,
    erw [← add, ← mul, ←  mul, ← mul, ← add, left_distrib]
  end,
  right_distrib := λ x y z,
  begin
    rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩, rcases hf z with ⟨z, rfl⟩,
    erw [← add, ← mul, ←  mul, ← mul, ← add, right_distrib]
  end,
  zero_mul      := λ x, by { rcases hf x with ⟨x, rfl⟩, erw [← zero, ← mul, zero_mul] },
  mul_zero      := λ x, by { rcases hf x with ⟨x, rfl⟩, erw [← zero, ← mul, mul_zero] },
  ..add_comm_monoid_of_surjective f hf zero add, ..monoid_of_surjective f hf one mul }

/-- A type endowed with `0`, `1`, `+` and `*` is a commutative semiring,
if it admits a surjective map that preserves `0`, `1`, `+` and `*` from a commutative semiring. -/
def comm_semiring_of_surjective [comm_semiring R₁] (f : R₁ → R₂) (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semiring R₂ :=
{ ..comm_monoid_of_surjective f hf one mul, ..semiring_of_surjective f hf zero one add mul }

variables [has_neg R₂]

/-- A type endowed with `0`, `1`, `+`, `*` and `-` is a ring,
if it admits a surjective map that preserves `0`, `1`, `+`, `*` and `-` from a ring. -/
def ring_of_surjective [ring R₁] (f : R₁ → R₂) (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) :
  ring R₂ :=
{ ..add_comm_group_of_surjective f hf zero add neg, ..semiring_of_surjective f hf zero one add mul }

/-- A type endowed with `0`, `1`, `+`, `*` and `-` is a commutative ring,
if it admits a surjective map that preserves `0`, `1`, `+`, `*` and `-` from a commutative ring. -/
def comm_ring_of_surjective [comm_ring R₁] (f : R₁ → R₂) (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) :
  comm_ring R₂ :=
{ ..comm_monoid_of_surjective f hf one mul, ..ring_of_surjective f hf zero one add mul neg }

end
