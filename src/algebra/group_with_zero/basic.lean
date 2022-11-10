/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group.inj_surj
import algebra.group_with_zero.defs
import algebra.group.order_synonym

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

set_option old_structure_cmd true
open_locale classical
open function

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

section

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

lemma mul_eq_zero_of_left (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

lemma mul_eq_zero_of_right (a : M₀) (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

lemma left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 := mt (λ h, mul_eq_zero_of_left h b)

lemma right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 := mt (mul_eq_zero_of_right a)

lemma ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

lemma mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) :
  a * b = 0 :=
if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
lemma zero_mul_eq_const : ((*) (0 : M₀)) = function.const _ 0 := funext zero_mul

/-- To match `mul_one_eq_id`. -/
lemma mul_zero_eq_const : (* (0 : M₀)) = function.const _ 0 := funext mul_zero

end mul_zero_class

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected lemma function.injective.no_zero_divisors [has_mul M₀] [has_zero M₀]
  [has_mul M₀'] [has_zero M₀'] [no_zero_divisors M₀']
  (f : M₀ → M₀') (hf : injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  no_zero_divisors M₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y H,
  have f x * f y = 0, by rw [← mul, H, zero],
  (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (λ H, hf $ by rwa zero)  (λ H, hf $ by rwa zero) }

section has_mul

variables [has_mul M₀] [has_zero M₀] [no_zero_divisors M₀] {a b : M₀}

lemma eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
(eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

@[field_simps] theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
mt eq_zero_or_eq_zero_of_mul_eq_zero $ not_or_distrib.mpr ⟨ha, hb⟩

end has_mul

namespace ne_zero

instance mul [has_zero M₀] [has_mul M₀] [no_zero_divisors M₀] {x y : M₀}
  [ne_zero x] [ne_zero y] : ne_zero (x * y) :=
⟨mul_ne_zero out out⟩

end ne_zero

section

variables [mul_zero_class M₀] [no_zero_divisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨eq_zero_or_eq_zero_of_mul_eq_zero,
  λo, o.elim (λ h, mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
mul_eq_zero.not.trans not_or_distrib

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
mul_eq_zero.trans $ (or_comm _ _).trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
mul_eq_zero_comm.not

lemma mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
lemma zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
lemma mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not
lemma zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not

end

end

section

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

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
lemma eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 :=
by rw [← mul_one a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def unique_of_zero_eq_one (h : (0 : M₀) = 1) : unique M₀ :=
{ default := 0, uniq := eq_zero_of_zero_eq_one h }

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ subsingleton M₀ :=
⟨λ h, @unique.subsingleton _ (unique_of_zero_eq_one h), λ h, @subsingleton.elim _ h _ _⟩

alias subsingleton_iff_zero_eq_one ↔ subsingleton_of_zero_eq_one _

lemma eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
@subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
lemma zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ (∀a:M₀, a = 0) :=
not_or_of_imp eq_zero_of_zero_eq_one
end

section

variables [mul_zero_one_class M₀] [nontrivial M₀] {a b : M₀}

variable (M₀)

/-- In a nontrivial monoid with zero, zero and one are different. -/
instance ne_zero.one : ne_zero (1 : M₀) :=
⟨begin
  assume h,
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩,
  apply hx,
  calc x = 1 * x : by rw [one_mul]
  ... = 0 : by rw [h, zero_mul]
  ... = 1 * y : by rw [h, zero_mul]
  ... = y : by rw [one_mul]
end⟩

variable {M₀}

lemma left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
left_ne_zero_of_mul $ ne_zero_of_eq_one h

lemma right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
right_ne_zero_of_mul $ ne_zero_of_eq_one h

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
protected lemma pullback_nonzero [has_zero M₀'] [has_one M₀']
  (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) : nontrivial M₀' :=
⟨⟨0, 1, mt (congr_arg f) $ by { rw [zero, one], exact zero_ne_one }⟩⟩

end

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

@[priority 10] -- see Note [lower instance priority]
instance cancel_monoid_with_zero.to_no_zero_divisors : no_zero_divisors M₀ :=
⟨λ a b ab0, by { by_cases a = 0, { left, exact h }, right,
  apply cancel_monoid_with_zero.mul_left_cancel_of_ne_zero h, rw [ab0, mul_zero], }⟩

lemma mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := (mul_left_injective₀ hc).eq_iff
lemma mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := (mul_right_injective₀ ha).eq_iff

@[simp] lemma mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 :=
by by_cases hc : c = 0; [simp [hc], simp [mul_left_inj', hc]]

@[simp] lemma mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 :=
by by_cases ha : a = 0; [simp [ha], simp [mul_right_inj', ha]]

lemma mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
     ...       ↔ b = 1 ∨ a = 0 : mul_eq_mul_left_iff

lemma mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
calc a * b = b ↔ a * b = 1 * b : by rw one_mul
     ...       ↔ a = 1 ∨ b = 0 : mul_eq_mul_right_iff

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

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_left_cancel₀ ha $ h₂.symm ▸ (mul_one a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_right_cancel₀ ha $ h₂.symm ▸ (one_mul a).symm

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

@[simp] lemma mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) :
  (a * b) * b⁻¹ = a :=
calc (a * b) * b⁻¹ = a * (b * b⁻¹) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) :
  a * (a⁻¹ * b) = b :=
calc a * (a⁻¹ * b) = (a * a⁻¹) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

lemma inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 :=
assume a_eq_0, by simpa [a_eq_0] using mul_inv_cancel h

@[simp] lemma inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
calc a⁻¹ * a = (a⁻¹ * a) * a⁻¹ * a⁻¹⁻¹ : by simp [inv_ne_zero h]
         ... = a⁻¹ * a⁻¹⁻¹             : by simp [h]
         ... = 1                       : by simp [inv_ne_zero h]

lemma group_with_zero.mul_left_injective (h : x ≠ 0) :
  function.injective (λ y, x * y) :=
λ y y' w, by simpa only [←mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (λ y, x⁻¹ * y) w

lemma group_with_zero.mul_right_injective (h : x ≠ 0) :
  function.injective (λ y, y * x) :=
λ y y' w, by simpa only [mul_assoc, mul_inv_cancel h, mul_one] using congr_arg (λ y, y * x⁻¹) w

@[simp] lemma inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) :
  (a * b⁻¹) * b = a :=
calc (a * b⁻¹) * b = a * (b⁻¹ * b) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) :
  a⁻¹ * (a * b) = b :=
calc a⁻¹ * (a * b) = (a⁻¹ * a) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

private lemma inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
by rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

@[priority 100] -- See note [lower instance priority]
instance group_with_zero.to_division_monoid : division_monoid G₀ :=
{ inv := has_inv.inv,
  inv_inv := λ a, begin
    by_cases h : a = 0,
    { simp [h] },
    { exact left_inv_eq_right_inv (inv_mul_cancel $ inv_ne_zero h) (inv_mul_cancel h) }
  end,
  mul_inv_rev := λ a b, begin
    by_cases ha : a = 0, { simp [ha] },
    by_cases hb : b = 0, { simp [hb] },
    refine inv_eq_of_mul _,
    simp [mul_assoc, ha, hb]
  end,
  inv_eq_of_mul := λ a b, inv_eq_of_mul,
  ..‹group_with_zero G₀› }

end group_with_zero

section group_with_zero
variables [group_with_zero G₀] {a b c : G₀}

@[simp] lemma zero_div (a : G₀) : 0 / a = 0 :=
by rw [div_eq_mul_inv, zero_mul]

@[simp] lemma div_zero (a : G₀) : a / 0 = 0 :=
by rw [div_eq_mul_inv, inv_zero, mul_zero]

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_assoc, mul_inv_cancel h, mul_one] }
end

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_inv_cancel h, one_mul] }
end

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp] lemma inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [inv_mul_cancel h, one_mul] }
end

/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp] lemma mul_self_div_self (a : G₀) : a * a / a = a :=
by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp] lemma div_self_mul_self (a : G₀) : a / a * a = a :=
by rw [div_eq_mul_inv, mul_inv_mul_self a]

local attribute [simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp] lemma div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
calc a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ : by simp [mul_inv_rev]
... = a⁻¹ : inv_mul_mul_self _

lemma one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 :=
by simpa only [one_div] using inv_ne_zero h

@[simp] lemma inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 :=
by rw [inv_eq_iff_inv_eq, inv_zero, eq_comm]

@[simp] lemma zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
eq_comm.trans $ inv_eq_zero.trans eq_comm

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma div_div_self (a : G₀) : a / (a / a) = a :=
begin
  rw div_div_eq_mul_div,
  exact mul_self_div_self a
end

lemma ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, div_zero] at h, contradiction end

lemma eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
classical.by_cases
  (assume ha, ha)
  (assume ha, ((one_div_ne_zero ha) h).elim)

lemma mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : surjective (λ g, a * g) :=
λ g, ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel h]⟩

lemma mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : surjective (λ g, g * a) :=
λ g, ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel h]⟩

end group_with_zero

section comm_group_with_zero -- comm
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

lemma div_mul_eq_mul_div₀ (a b c : G₀) : (a / c) * b = a * b / c :=
by simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

end comm_group_with_zero

/-! ### Order dual -/

open order_dual

instance [h : mul_zero_class α] : mul_zero_class αᵒᵈ := h
instance [h : mul_zero_one_class α] : mul_zero_one_class αᵒᵈ := h
instance [has_mul α] [has_zero α] [h : no_zero_divisors α] : no_zero_divisors αᵒᵈ := h
instance [h : semigroup_with_zero α] : semigroup_with_zero αᵒᵈ := h
instance [h : monoid_with_zero α] : monoid_with_zero αᵒᵈ := h
instance [h : cancel_monoid_with_zero α] : cancel_monoid_with_zero αᵒᵈ := h
instance [h : comm_monoid_with_zero α] : comm_monoid_with_zero αᵒᵈ := h
instance [h : cancel_comm_monoid_with_zero α] : cancel_comm_monoid_with_zero αᵒᵈ := h
instance [h : group_with_zero α] : group_with_zero αᵒᵈ := h
instance [h : comm_group_with_zero α] : comm_group_with_zero αᵒᵈ := h

/-! ### Lexicographic order -/

instance [h : mul_zero_class α] : mul_zero_class (lex α) := h
instance [h : mul_zero_one_class α] : mul_zero_one_class (lex α) := h
instance [has_mul α] [has_zero α] [h : no_zero_divisors α] : no_zero_divisors (lex α) := h
instance [h : semigroup_with_zero α] : semigroup_with_zero (lex α) := h
instance [h : monoid_with_zero α] : monoid_with_zero (lex α) := h
instance [h : cancel_monoid_with_zero α] : cancel_monoid_with_zero (lex α) := h
instance [h : comm_monoid_with_zero α] : comm_monoid_with_zero (lex α) := h
instance [h : cancel_comm_monoid_with_zero α] : cancel_comm_monoid_with_zero (lex α) := h
instance [h : group_with_zero α] : group_with_zero (lex α) := h
instance [h : comm_group_with_zero α] : comm_group_with_zero (lex α) := h
