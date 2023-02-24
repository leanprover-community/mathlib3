/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group.inj_surj
import algebra.group_with_zero.defs

/-!
# Lifting groups with zero along injective/surjective maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function

variables {M₀ G₀ M₀' G₀' : Type*}

section mul_zero_class

variables [mul_zero_class M₀] {a b : M₀}

/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_zero_class [has_mul M₀'] [has_zero M₀'] (f : M₀' → M₀)
  (hf : injective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_class M₀' :=
{ mul := (*),
  zero := 0,
  zero_mul := λ a, hf $ by simp only [mul, zero, zero_mul],
  mul_zero := λ a, hf $ by simp only [mul, zero, mul_zero] }

/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_zero_class [has_mul M₀'] [has_zero M₀'] (f : M₀ → M₀')
  (hf : surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_class M₀' :=
{ mul := (*),
  zero := 0,
  mul_zero := hf.forall.2 $ λ x, by simp only [← zero, ← mul, mul_zero],
  zero_mul := hf.forall.2 $ λ x, by simp only [← zero, ← mul, zero_mul] }

end mul_zero_class

section no_zero_divisors

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected lemma function.injective.no_zero_divisors [has_mul M₀] [has_zero M₀]
  [has_mul M₀'] [has_zero M₀'] [no_zero_divisors M₀']
  (f : M₀ → M₀') (hf : injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  no_zero_divisors M₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y H,
  have f x * f y = 0, by rw [← mul, H, zero],
  (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (λ H, hf $ by rwa zero)  (λ H, hf $ by rwa zero) }

end no_zero_divisors

section mul_zero_one_class

variables [mul_zero_one_class M₀]

/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_zero_one_class [has_mul M₀'] [has_zero M₀'] [has_one M₀']
  (f : M₀' → M₀)
  (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_one_class M₀' :=
{ ..hf.mul_zero_class f zero mul, ..hf.mul_one_class f one mul }

/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_zero_one_class [has_mul M₀'] [has_zero M₀'] [has_one M₀']
  (f : M₀ → M₀')
  (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_one_class M₀' :=
{ ..hf.mul_zero_class f zero mul, ..hf.mul_one_class f one mul }

end mul_zero_one_class

section semigroup_with_zero

/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.semigroup_with_zero
  [has_zero M₀'] [has_mul M₀'] [semigroup_with_zero M₀] (f : M₀' → M₀) (hf : injective f)
  (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup_with_zero M₀' :=
{ .. hf.mul_zero_class f zero mul,
  .. ‹has_zero M₀'›,
  .. hf.semigroup f mul }

/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.semigroup_with_zero
  [semigroup_with_zero M₀] [has_zero M₀'] [has_mul M₀'] (f : M₀ → M₀') (hf : surjective f)
  (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup_with_zero M₀' :=
{ .. hf.mul_zero_class f zero mul,
  .. ‹has_zero M₀'›,
  .. hf.semigroup f mul }

end semigroup_with_zero

section monoid_with_zero

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [has_pow M₀' ℕ] [monoid_with_zero M₀]
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  monoid_with_zero M₀' :=
{ .. hf.monoid f one mul npow, .. hf.mul_zero_class f zero mul }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [has_pow M₀' ℕ] [monoid_with_zero M₀]
  (f : M₀ → M₀') (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  monoid_with_zero M₀' :=
{ .. hf.monoid f one mul npow, .. hf.mul_zero_class f zero mul }

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [has_pow M₀' ℕ] [comm_monoid_with_zero M₀]
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid f one mul npow, .. hf.mul_zero_class f zero mul }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [has_pow M₀' ℕ] [comm_monoid_with_zero M₀]
  (f : M₀ → M₀') (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid f one mul npow, .. hf.mul_zero_class f zero mul }

end monoid_with_zero

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero M₀] {a b c : M₀}

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.cancel_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [has_pow M₀' ℕ] (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  cancel_monoid_with_zero M₀' :=
{ mul_left_cancel_of_ne_zero := λ x y z hx H, hf $ mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) $
    by erw [← mul, ← mul, H]; refl,
  mul_right_cancel_of_ne_zero := λ x y z hx H, hf $ mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) $
    by erw [← mul, ← mul, H]; refl,
  .. hf.monoid f one mul npow, .. hf.mul_zero_class f zero mul }

end cancel_monoid_with_zero

section cancel_comm_monoid_with_zero

variables [cancel_comm_monoid_with_zero M₀] {a b c : M₀}

/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.cancel_comm_monoid_with_zero
  [has_zero M₀'] [has_mul M₀'] [has_one M₀'] [has_pow M₀' ℕ]
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  cancel_comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid_with_zero f zero one mul npow,
  .. hf.cancel_monoid_with_zero f zero one mul npow }

end cancel_comm_monoid_with_zero

section group_with_zero
variables [group_with_zero G₀] {a b c g h x : G₀}

/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] [has_pow G₀' ℕ] [has_pow G₀' ℤ]
  (f : G₀' → G₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  group_with_zero G₀' :=
{ inv_zero := hf $ by erw [inv, zero, inv_zero],
  mul_inv_cancel := λ x hx, hf $ by erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)],
  .. hf.monoid_with_zero f zero one mul npow,
  .. hf.div_inv_monoid f one mul inv div npow zpow,
  .. pullback_nonzero f zero one, }

/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] [has_pow G₀' ℕ] [has_pow G₀' ℤ]
  (h01 : (0:G₀') ≠ 1) (f : G₀ → G₀') (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n):
  group_with_zero G₀' :=
{ inv_zero := by erw [← zero, ← inv, inv_zero],
  mul_inv_cancel := hf.forall.2 $ λ x hx,
    by erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) $ trans_rel_left ne hx zero.symm)];
      exact one,
  exists_pair_ne := ⟨0, 1, h01⟩,
  .. hf.monoid_with_zero f zero one mul npow,
  .. hf.div_inv_monoid f one mul inv div npow zpow }

end group_with_zero

section comm_group_with_zero
variables [comm_group_with_zero G₀] {a b c d : G₀}

/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] [has_pow G₀' ℕ] [has_pow G₀' ℤ]
  (f : G₀' → G₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  comm_group_with_zero G₀' :=
{ .. hf.group_with_zero f zero one mul inv div npow zpow, .. hf.comm_semigroup f mul }

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def function.surjective.comm_group_with_zero [has_zero G₀'] [has_mul G₀']
  [has_one G₀'] [has_inv G₀'] [has_div G₀'] [has_pow G₀' ℕ] [has_pow G₀' ℤ]
  (h01 : (0:G₀') ≠ 1) (f : G₀ → G₀') (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) :
  comm_group_with_zero G₀' :=
{ .. hf.group_with_zero h01 f zero one mul inv div npow zpow, .. hf.comm_semigroup f mul }

end comm_group_with_zero
