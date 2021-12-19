/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group.defs
import logic.function.basic

/-!
# Lifting algebraic data classes along injective/surjective maps

This file provides definitions that are meant to deal with
situations such as the following:

Suppose that `G` is a group, and `H` is a type endowed with
`has_one H`, `has_mul H`, and `has_inv H`.
Suppose furthermore, that `f : G → H` is a surjective map
that respects the multiplication, and the unit elements.
Then `H` satisfies the group axioms.

The relevant definition in this case is `function.surjective.group`.
Dually, there is also `function.injective.group`.
And there are versions for (additive) (commutative) semigroups/monoids.
-/

namespace function

/-!
### Injective
-/

namespace injective

variables {M₁ : Type*} {M₂ : Type*} [has_mul M₁]

/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `+` is an additive semigroup,
if it admits an injective map that preserves `+` to an additive semigroup."]
protected def semigroup [semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup M₁ :=
{ mul_assoc := λ x y z, hf $ by erw [mul, mul, mul, mul, mul_assoc],
  ..‹has_mul M₁› }

/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `+` is an additive commutative semigroup,
if it admits an injective map that preserves `+` to an additive commutative semigroup."]
protected def comm_semigroup [comm_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semigroup M₁ :=
{ mul_comm := λ x y, hf $ by erw [mul, mul, mul_comm],
  .. hf.semigroup f mul }

/-- A type endowed with `*` is a left cancel semigroup,
if it admits an injective map that preserves `*` to a left cancel semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive add_left_cancel_semigroup
"A type endowed with `+` is an additive left cancel semigroup,
if it admits an injective map that preserves `+` to an additive left cancel semigroup."]
protected def left_cancel_semigroup [left_cancel_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  left_cancel_semigroup M₁ :=
{ mul := (*),
  mul_left_cancel := λ x y z H, hf $ (mul_right_inj (f x)).1 $ by erw [← mul, ← mul, H]; refl,
  .. hf.semigroup f mul }

/-- A type endowed with `*` is a right cancel semigroup,
if it admits an injective map that preserves `*` to a right cancel semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive add_right_cancel_semigroup
"A type endowed with `+` is an additive right cancel semigroup,
if it admits an injective map that preserves `+` to an additive right cancel semigroup."]
protected def right_cancel_semigroup [right_cancel_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  right_cancel_semigroup M₁ :=
{ mul := (*),
  mul_right_cancel := λ x y z H, hf $ (mul_left_inj (f y)).1 $ by erw [← mul, ← mul, H]; refl,
  .. hf.semigroup f mul }

variables [has_one M₁]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits an injective map that preserves `1` and `*` to a mul_one_class.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an add_zero_class,
if it admits an injective map that preserves `0` and `+` to an add_zero_class."]
protected def mul_one_class [mul_one_class M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  mul_one_class M₁ :=
{ one_mul := λ x, hf $ by erw [mul, one, one_mul],
  mul_one := λ x, hf $ by erw [mul, one, mul_one],
  ..‹has_one M₁›, ..‹has_mul M₁› }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive monoid,
if it admits an injective map that preserves `0` and `+` to an additive monoid."]
protected def monoid [monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid M₁ :=
{ .. hf.semigroup f mul, .. hf.mul_one_class f one mul }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
This version takes a custom `npow` as a `[has_pow M₁ ℕ]` argument.
See note [reducible non-instances]. -/
@[reducible, to_additive add_monoid_smul
"A type endowed with `0` and `+` is an additive monoid,
if it admits an injective map that preserves `0` and `+` to an additive monoid.
This version takes a custom `nsmul` as a `[has_scalar ℕ M₁]` argument."]
protected def monoid_pow [has_pow M₁ ℕ] [monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  monoid M₁ :=
{ npow := λ n x, x ^ n,
  npow_zero' := λ x, hf $ by erw [npow, one, pow_zero],
  npow_succ' := λ n x, hf $ by erw [npow, pow_succ, mul, npow],
  .. hf.monoid f one mul }

/-- A type endowed with `1` and `*` is a left cancel monoid,
if it admits an injective map that preserves `1` and `*` to a left cancel monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive add_left_cancel_monoid
"A type endowed with `0` and `+` is an additive left cancel monoid,
if it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def left_cancel_monoid [left_cancel_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  left_cancel_monoid M₁ :=
{ .. hf.left_cancel_semigroup f mul, .. hf.monoid f one mul }

/-- A type endowed with `1` and `*` is a right cancel monoid,
if it admits an injective map that preserves `1` and `*` to a right cancel monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive add_right_cancel_monoid
"A type endowed with `0` and `+` is an additive left cancel monoid,
if it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def right_cancel_monoid [right_cancel_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  right_cancel_monoid M₁ :=
{ .. hf.right_cancel_semigroup f mul, .. hf.monoid f one mul }

/-- A type endowed with `1` and `*` is a cancel monoid,
if it admits an injective map that preserves `1` and `*` to a cancel monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive add_cancel_monoid
"A type endowed with `0` and `+` is an additive left cancel monoid,
if it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def cancel_monoid [cancel_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  cancel_monoid M₁ :=
{ .. hf.left_cancel_monoid f one mul, .. hf.right_cancel_monoid f one mul }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive commutative monoid,
if it admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
protected def comm_monoid [comm_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid M₁ :=
{ .. hf.comm_semigroup f mul, .. hf.monoid f one mul }

/-- A type endowed with `1` and `*` is a cancel commutative monoid,
if it admits an injective map that preserves `1` and `*` to a cancel commutative monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive add_cancel_comm_monoid
"A type endowed with `0` and `+` is an additive cancel commutative monoid,
if it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid."]
protected def cancel_comm_monoid [cancel_comm_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  cancel_comm_monoid M₁ :=
{ .. hf.left_cancel_semigroup f mul, .. hf.comm_monoid f one mul }

variables [has_inv M₁] [has_div M₁]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
See note [reducible non-instances]. -/
@[reducible, to_additive sub_neg_monoid
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`
if it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `sub_neg_monoid`."]
protected def div_inv_monoid [div_inv_monoid M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  div_inv_monoid M₁ :=
{ div_eq_mul_inv := λ x y, hf $ by erw [div, mul, inv, div_eq_mul_inv],
  .. hf.monoid f one mul, .. ‹has_inv M₁›, .. ‹has_div M₁› }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible, to_additive sub_neg_monoid_smul
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`
if it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `sub_neg_monoid`.
This version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and
`[has_scalar ℤ M₁]` arguments."]
protected def div_inv_monoid_pow [has_pow M₁ ℕ] [has_pow M₁ ℤ] [div_inv_monoid M₂]
  (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  div_inv_monoid M₁ :=
{ zpow := λ n x, x ^ n,
  zpow_zero' := λ x, hf $ by erw [zpow, zpow_zero, one],
  zpow_succ' := λ n x, hf $ by erw [zpow, mul, zpow_of_nat, pow_succ, zpow, zpow_of_nat],
  zpow_neg' := λ n x, hf $ by erw [zpow, zpow_neg_succ_of_nat, inv, zpow, zpow_coe_nat],
  .. hf.monoid_pow f one mul npow,
  .. hf.div_inv_monoid f one mul inv div }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive group,
if it admits an injective map that preserves `0` and `+` to an additive group."]
protected def group [group M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  group M₁ :=
{ mul_left_inv := λ x, hf $ by erw [mul, inv, mul_left_inv, one],
  .. hf.div_inv_monoid f one mul inv div }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible, to_additive add_group_smul
"A type endowed with `0` and `+` is an additive group,
if it admits an injective map that preserves `0` and `+` to an additive group.
This version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and
`[has_scalar ℤ M₁]` arguments."]
protected def group_pow [has_pow M₁ ℕ] [has_pow M₁ ℤ] [group M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  group M₁ :=
{ .. hf.div_inv_monoid_pow f one mul inv div npow zpow,
  .. hf.group f one mul inv div }

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive commutative group,
if it admits an injective map that preserves `0` and `+` to an additive commutative group."]
protected def comm_group [comm_group M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  comm_group M₁ :=
{ .. hf.comm_monoid f one mul, .. hf.group f one mul inv div }

end injective

/-!
### Surjective
-/

namespace surjective
variables {M₁ : Type*} {M₂ : Type*} [has_mul M₂]

/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `+` is an additive semigroup,
if it admits a surjective map that preserves `+` from an additive semigroup."]
protected def semigroup [semigroup M₁] (f : M₁ → M₂) (hf : surjective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup M₂ :=
{ mul_assoc := hf.forall₃.2 $ λ x y z, by simp only [← mul, mul_assoc],
  ..‹has_mul M₂› }

/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `+` is an additive commutative semigroup,
if it admits a surjective map that preserves `+` from an additive commutative semigroup."]
protected def comm_semigroup [comm_semigroup M₁] (f : M₁ → M₂) (hf : surjective f)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semigroup M₂ :=
{ mul_comm := hf.forall₂.2 $ λ x y, by erw [← mul, ←  mul, mul_comm],
  .. hf.semigroup f mul }

variables [has_one M₂]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits a surjective map that preserves `1` and `*` from a mul_one_class.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an add_zero_class,
if it admits a surjective map that preserves `0` and `+` to an add_zero_class."]
protected def mul_one_class [mul_one_class M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  mul_one_class M₂ :=
{ one_mul := hf.forall.2 $ λ x, by erw [← one, ← mul, one_mul],
  mul_one := hf.forall.2 $ λ x, by erw [← one, ← mul, mul_one],
  ..‹has_one M₂›, ..‹has_mul M₂› }

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` from a monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive monoid,
if it admits a surjective map that preserves `0` and `+` to an additive monoid."]
protected def monoid [monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid M₂ :=
{ .. hf.semigroup f mul, .. hf.mul_one_class f one mul }

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` to a monoid.
This version takes a custom `npow` as a `[has_pow M₂ ℕ]` argument.
See note [reducible non-instances]. -/
@[reducible, to_additive add_monoid_smul
"A type endowed with `0` and `+` is an additive monoid,
if it admits a surjective map that preserves `0` and `+` to an additive monoid.
This version takes a custom `nsmul` as a `[has_scalar ℕ M₂]` argument."]
protected def monoid_pow [has_pow M₂ ℕ] [monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  monoid M₂ :=
{ npow := λ n x, x ^ n,
  npow_zero' := hf.forall.2 $ λ x, by erw [←npow, pow_zero, ←one],
  npow_succ' := λ n, hf.forall.2 $ λ x, by erw [←npow, pow_succ, ←npow, ←mul],
  .. hf.monoid f one mul }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive commutative monoid,
if it admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected def comm_monoid [comm_monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid M₂ :=
{ .. hf.comm_semigroup f mul, .. hf.monoid f one mul }

variables [has_inv M₂] [has_div M₂]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a `div_inv_monoid`
See note [reducible non-instances]. -/
@[reducible, to_additive sub_neg_monoid
"A type endowed with `0`, `+`, and `-` (unary and binary) is an additive group,
if it admits a surjective map that preserves `0`, `+`, and `-` from a `sub_neg_monoid`"]
protected def div_inv_monoid [div_inv_monoid M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  div_inv_monoid M₂ :=
{ div_eq_mul_inv := hf.forall₂.2 $ λ x y, by erw [← inv, ← mul, ← div, div_eq_mul_inv],
  .. hf.monoid f one mul, .. ‹has_div M₂›, .. ‹has_inv M₂› }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
This version takes custom `npow` and `zpow` as `[has_pow M₂ ℕ]` and `[has_pow M₂ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible, to_additive sub_neg_monoid_smul
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`
if it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `sub_neg_monoid`.
This version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₂]` and
`[has_scalar ℤ M₂]` arguments."]
protected def div_inv_monoid_pow [has_pow M₂ ℕ] [has_pow M₂ ℤ] [div_inv_monoid M₁]
  (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  div_inv_monoid M₂ :=
{ zpow := λ n x, x ^ n,
  zpow_zero' := hf.forall.2 $ λ x, by erw [←zpow, zpow_zero, ←one],
  zpow_succ' := λ n, hf.forall.2 $ λ x, by
    erw [←zpow, ←zpow, zpow_of_nat, zpow_of_nat, pow_succ, ←mul],
  zpow_neg' := λ n, hf.forall.2 $ λ x, by
    erw [←zpow, ←zpow, zpow_neg_succ_of_nat, zpow_coe_nat, inv],
  .. hf.monoid_pow f one mul npow,
  .. hf.div_inv_monoid f one mul inv div }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a group.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0`, `+`, and unary `-` is an additive group,
if it admits a surjective map that preserves `0`, `+`, and `-` from an additive group."]
protected def group [group M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  group M₂ :=
{ mul_left_inv := hf.forall.2 $ λ x, by erw [← inv, ← mul, mul_left_inv, one]; refl,
  .. hf.div_inv_monoid f one mul inv div }
/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` to a group.
This version takes custom `npow` and `zpow` as `[has_pow M₂ ℕ]` and `[has_pow M₂ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible, to_additive add_group_smul
"A type endowed with `0` and `+` is an additive group,
if it admits a surjective map that preserves `0` and `+` to an additive group.
This version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₂]` and
`[has_scalar ℤ M₂]` arguments."]
protected def group_pow [has_pow M₂ ℕ] [has_pow M₂ ℤ] [group M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  group M₂ :=
{ .. hf.div_inv_monoid_pow f one mul inv div npow zpow,
  .. hf.group f one mul inv div }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group.
See note [reducible non-instances]. -/
@[reducible, to_additive
"A type endowed with `0` and `+` is an additive commutative group,
if it admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected def comm_group [comm_group M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  comm_group M₂ :=
{ .. hf.comm_monoid f one mul, .. hf.group f one mul inv div }

end surjective

end function
