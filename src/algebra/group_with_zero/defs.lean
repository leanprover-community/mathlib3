/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group.defs
import logic.nontrivial
import algebra.ne_zero

/-!
# Typeclasses for groups with an adjoined zero element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`
-/

set_option old_structure_cmd true

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `group_with_zero.div'` cannot contain a universe metavariable.
variables {G₀ : Type u} {M₀ M₀' G₀' : Type*}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
@[protect_proj, ancestor has_mul has_zero]
class mul_zero_class (M₀ : Type*) extends has_mul M₀, has_zero M₀ :=
(zero_mul : ∀ a : M₀, 0 * a = 0)
(mul_zero : ∀ a : M₀, a * 0 = 0)

section mul_zero_class

variables [mul_zero_class M₀] {a b : M₀}

@[ematch, simp] lemma zero_mul (a : M₀) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[ematch, simp] lemma mul_zero (a : M₀) : a * 0 = 0 :=
mul_zero_class.mul_zero a

end mul_zero_class

/-- A mixin for left cancellative multiplication by nonzero elements. -/
@[protect_proj] class is_left_cancel_mul_zero (M₀ : Type u) [has_mul M₀] [has_zero M₀] : Prop :=
(mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c)

section is_left_cancel_mul_zero

variables [has_mul M₀] [has_zero M₀] [is_left_cancel_mul_zero M₀] {a b c : M₀}

lemma mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
is_left_cancel_mul_zero.mul_left_cancel_of_ne_zero ha h

lemma mul_right_injective₀ (ha : a ≠ 0) : function.injective ((*) a) :=
λ b c, mul_left_cancel₀ ha

end is_left_cancel_mul_zero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
@[protect_proj] class is_right_cancel_mul_zero (M₀ : Type u) [has_mul M₀] [has_zero M₀] : Prop :=
(mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c)

section is_right_cancel_mul_zero

variables [has_mul M₀] [has_zero M₀] [is_right_cancel_mul_zero M₀] {a b c : M₀}

lemma mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
is_right_cancel_mul_zero.mul_right_cancel_of_ne_zero hb h

lemma mul_left_injective₀ (hb : b ≠ 0) : function.injective (λ a, a * b) :=
λ a c, mul_right_cancel₀ hb

end is_right_cancel_mul_zero

/-- A mixin for cancellative multiplication by nonzero elements. -/
@[protect_proj] class is_cancel_mul_zero (M₀ : Type u) [has_mul M₀] [has_zero M₀]
  extends is_left_cancel_mul_zero M₀, is_right_cancel_mul_zero M₀ : Prop

section comm_semigroup_with_zero

variables [comm_semigroup M₀] [has_zero M₀]

lemma is_left_cancel_mul_zero.to_is_right_cancel_mul_zero [is_left_cancel_mul_zero M₀] :
  is_right_cancel_mul_zero M₀ :=
⟨λ a b c ha h, mul_left_cancel₀ ha $ (mul_comm _ _).trans $ (h.trans (mul_comm _ _))⟩

lemma is_right_cancel_mul_zero.to_is_left_cancel_mul_zero [is_right_cancel_mul_zero M₀] :
  is_left_cancel_mul_zero M₀ :=
⟨λ a b c ha h, mul_right_cancel₀ ha $ (mul_comm _ _).trans $ (h.trans (mul_comm _ _))⟩

lemma is_left_cancel_mul_zero.to_is_cancel_mul_zero [is_left_cancel_mul_zero M₀] :
  is_cancel_mul_zero M₀ :=
{ .. ‹is_left_cancel_mul_zero M₀›, .. is_left_cancel_mul_zero.to_is_right_cancel_mul_zero }

lemma is_right_cancel_mul_zero.to_is_cancel_mul_zero [is_right_cancel_mul_zero M₀] :
  is_cancel_mul_zero M₀ :=
{ .. ‹is_right_cancel_mul_zero M₀›, .. is_right_cancel_mul_zero.to_is_left_cancel_mul_zero }

end comm_semigroup_with_zero

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class no_zero_divisors (M₀ : Type*) [has_mul M₀] [has_zero M₀] : Prop :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0)

export no_zero_divisors (eq_zero_or_eq_zero_of_mul_eq_zero)

/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
@[protect_proj, ancestor semigroup mul_zero_class]
class semigroup_with_zero (S₀ : Type*) extends semigroup S₀, mul_zero_class S₀.

/- By defining this _after_ `semigroup_with_zero`, we ensure that searches for `mul_zero_class` find
this class first. -/
/-- A typeclass for non-associative monoids with zero elements. -/
@[protect_proj, ancestor mul_one_class mul_zero_class]
class mul_zero_one_class (M₀ : Type*) extends mul_one_class M₀, mul_zero_class M₀.

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
@[protect_proj, ancestor monoid mul_zero_one_class]
class monoid_with_zero (M₀ : Type*) extends monoid M₀, mul_zero_one_class M₀.

@[priority 100] -- see Note [lower instance priority]
instance monoid_with_zero.to_semigroup_with_zero (M₀ : Type*) [monoid_with_zero M₀] :
  semigroup_with_zero M₀ :=
{ ..‹monoid_with_zero M₀› }

/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[protect_proj, ancestor monoid_with_zero]
class cancel_monoid_with_zero (M₀ : Type*) extends monoid_with_zero M₀ :=
(mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c)
(mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c)

/-- A `cancel_monoid_with_zero` satisfies `is_cancel_mul_zero`. -/
@[priority 100]
instance cancel_monoid_with_zero.to_is_cancel_mul_zero [cancel_monoid_with_zero M₀] :
  is_cancel_mul_zero M₀ :=
{ .. ‹cancel_monoid_with_zero M₀› }

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
@[protect_proj, ancestor comm_monoid monoid_with_zero]
class comm_monoid_with_zero (M₀ : Type*) extends comm_monoid M₀, monoid_with_zero M₀.

/-- A type `M` is a `cancel_comm_monoid_with_zero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
@[protect_proj, ancestor comm_monoid_with_zero cancel_monoid_with_zero]
class cancel_comm_monoid_with_zero (M₀ : Type*) extends comm_monoid_with_zero M₀ :=
(mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c)

@[priority 100]
instance cancel_comm_monoid_with_zero.to_cancel_monoid_with_zero
  [h : cancel_comm_monoid_with_zero M₀] : cancel_monoid_with_zero M₀ :=
{ .. h, .. @is_left_cancel_mul_zero.to_is_right_cancel_mul_zero M₀ _ _ { .. h } }

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
@[protect_proj, ancestor monoid_with_zero div_inv_monoid nontrivial]
class group_with_zero (G₀ : Type u) extends
  monoid_with_zero G₀, div_inv_monoid G₀, nontrivial G₀ :=
(inv_zero : (0 : G₀)⁻¹ = 0)
(mul_inv_cancel : ∀ a:G₀, a ≠ 0 → a * a⁻¹ = 1)

section group_with_zero

variables [group_with_zero G₀]

@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 :=
group_with_zero.inv_zero

@[simp] lemma mul_inv_cancel {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
group_with_zero.mul_inv_cancel a h

end group_with_zero

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
@[protect_proj, ancestor comm_monoid_with_zero group_with_zero]
class comm_group_with_zero (G₀ : Type*) extends comm_monoid_with_zero G₀, group_with_zero G₀.

section ne_zero

attribute [field_simps] two_ne_zero three_ne_zero four_ne_zero

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

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
lemma pullback_nonzero [has_zero M₀'] [has_one M₀']
  (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) : nontrivial M₀' :=
⟨⟨0, 1, mt (congr_arg f) $ by { rw [zero, one], exact zero_ne_one }⟩⟩

end ne_zero

section mul_zero_class

variables [mul_zero_class M₀]

lemma mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

lemma mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

variables [no_zero_divisors M₀] {a b : M₀}

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

end mul_zero_class
