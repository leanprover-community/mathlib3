/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.group.basic
import algebra.group_with_zero.defs
import data.int.cast.defs

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines semirings, rings and domains. This is analogous to `algebra.group.defs` and
`algebra.group.basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `distrib`: Typeclass for distributivity of multiplication over addition.
* `has_distrib_neg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `units`.
* `(non_unital_)(non_assoc_)(semi)ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`, `is_domain`, `nonzero`, `units`
-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

set_option old_structure_cmd true
open function

/-!
### `distrib` class
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj, ancestor has_mul has_add]
class distrib (R : Type*) extends has_mul R, has_add R :=
(left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c)
(right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c)

/-- A typeclass stating that multiplication is left distributive over addition. -/
@[protect_proj]
class left_distrib_class (R : Type*) [has_mul R] [has_add R] :=
(left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c)

/-- A typeclass stating that multiplication is right distributive over addition. -/
@[protect_proj]
class right_distrib_class (R : Type*) [has_mul R] [has_add R] :=
(right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c)

@[priority 100] -- see Note [lower instance priority]
instance distrib.left_distrib_class (R : Type*) [distrib R] : left_distrib_class R :=
⟨distrib.left_distrib⟩

@[priority 100] -- see Note [lower instance priority]
instance distrib.right_distrib_class (R : Type*) [distrib R] : right_distrib_class R :=
⟨distrib.right_distrib⟩

lemma left_distrib [has_mul R] [has_add R] [left_distrib_class R] (a b c : R) :
  a * (b + c) = a * b + a * c :=
left_distrib_class.left_distrib a b c

alias left_distrib ← mul_add

lemma right_distrib [has_mul R] [has_add R] [right_distrib_class R] (a b c : R) :
  (a + b) * c = a * c + b * c :=
right_distrib_class.right_distrib a b c

alias right_distrib ← add_mul

lemma distrib_three_right [has_mul R] [has_add R] [right_distrib_class R] (a b c d : R) :
  (a + b + c) * d = a * d + b * d + c * d :=
by simp [right_distrib]

/-!
### Semirings
-/

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj, ancestor add_comm_monoid distrib mul_zero_class]
class non_unital_non_assoc_semiring (α : Type u) extends
  add_comm_monoid α, distrib α, mul_zero_class α

/-- An associative but not-necessarily unital semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring semigroup_with_zero]
class non_unital_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, semigroup_with_zero α

/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring mul_zero_one_class]
class non_assoc_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, mul_zero_one_class α, add_comm_monoid_with_one α

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj, ancestor non_unital_semiring non_assoc_semiring monoid_with_zero]
class semiring (α : Type u) extends non_unital_semiring α, non_assoc_semiring α, monoid_with_zero α

section has_one_has_add

variables [has_one α] [has_add α]

lemma one_add_one_eq_two : 1 + 1 = (2 : α) := rfl

end has_one_has_add

section distrib_mul_one_class
variables [has_add α] [mul_one_class α]

lemma add_one_mul [right_distrib_class α] (a b : α) : (a + 1) * b = a * b + b :=
by rw [add_mul, one_mul]
lemma mul_add_one [left_distrib_class α] (a b : α) : a * (b + 1) = a * b + a :=
by rw [mul_add, mul_one]
lemma one_add_mul [right_distrib_class α] (a b : α) : (1 + a) * b = b + a * b :=
by rw [add_mul, one_mul]
lemma mul_one_add [left_distrib_class α] (a b : α) : a * (1 + b) = a + a * b :=
by rw [mul_add, mul_one]

theorem two_mul [right_distrib_class α] (n : α) : 2 * n = n + n :=
eq.trans (right_distrib 1 1 n) (by simp)

theorem bit0_eq_two_mul [right_distrib_class α] (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

theorem mul_two [left_distrib_class α] (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

end distrib_mul_one_class

section semiring
variables [semiring α]

@[to_additive] lemma mul_ite {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  a * (if P then b else c) = if P then a * b else a * c :=
by split_ifs; refl

@[to_additive] lemma ite_mul {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  (if P then a else b) * c = if P then a * c else b * c :=
by split_ifs; refl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp] lemma mul_boole {α} [mul_zero_one_class α] (P : Prop) [decidable P] (a : α) :
  a * (if P then 1 else 0) = if P then a else 0 :=
by simp

@[simp] lemma boole_mul {α} [mul_zero_one_class α] (P : Prop) [decidable P] (a : α) :
  (if P then 1 else 0) * a = if P then a else 0 :=
by simp

lemma ite_mul_zero_left {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = ite P a 0 * b :=
by { by_cases h : P; simp [h], }

lemma ite_mul_zero_right {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = a * ite P b 0 :=
by { by_cases h : P; simp [h], }

lemma ite_and_mul_zero {α : Type*} [mul_zero_class α]
  (P Q : Prop) [decidable P] [decidable Q] (a b : α) :
  ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 :=
by simp only [←ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

end semiring

/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj, ancestor non_unital_semiring comm_semigroup]
class non_unital_comm_semiring (α : Type u) extends non_unital_semiring α, comm_semigroup α

/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj, ancestor semiring comm_monoid]
class comm_semiring (α : Type u) extends semiring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_semiring.to_non_unital_comm_semiring [comm_semiring α] : non_unital_comm_semiring α :=
{ .. comm_semiring.to_comm_monoid α, .. comm_semiring.to_semiring α }

@[priority 100] -- see Note [lower instance priority]
instance comm_semiring.to_comm_monoid_with_zero [comm_semiring α] : comm_monoid_with_zero α :=
{ .. comm_semiring.to_comm_monoid α, .. comm_semiring.to_semiring α }

section comm_semiring
variables [comm_semiring α] {a b c : α}

lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
by simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

end comm_semiring

section has_distrib_neg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class has_distrib_neg (α : Type*) [has_mul α] extends has_involutive_neg α :=
(neg_mul : ∀ x y : α, -x * y = -(x * y))
(mul_neg : ∀ x y : α, x * -y = -(x * y))

section has_mul
variables [has_mul α] [has_distrib_neg α]

@[simp] lemma neg_mul (a b : α) : - a * b = - (a * b) :=
has_distrib_neg.neg_mul _ _

@[simp] lemma mul_neg (a b : α) : a * - b = - (a * b) :=
has_distrib_neg.mul_neg _ _

lemma neg_mul_neg (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
(neg_mul _ _).symm

lemma neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
(mul_neg _ _).symm

lemma neg_mul_comm (a b : α) : -a * b = a * -b :=
by simp

end has_mul

section mul_one_class
variables [mul_one_class α] [has_distrib_neg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a :=
by simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
lemma mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
lemma neg_one_mul (a : α) : -1 * a = -a := by simp

end mul_one_class

section mul_zero_class
variables [mul_zero_class α] [has_distrib_neg α]

@[priority 100]
instance mul_zero_class.neg_zero_class : neg_zero_class α :=
{ neg_zero := by rw [←zero_mul (0 : α), ←neg_mul, mul_zero, mul_zero],
  ..mul_zero_class.to_has_zero α,
  ..has_distrib_neg.to_has_involutive_neg α }

end mul_zero_class

end has_distrib_neg

/-!
### Rings
-/

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj, ancestor add_comm_group non_unital_non_assoc_semiring]
class non_unital_non_assoc_ring (α : Type u) extends
  add_comm_group α, non_unital_non_assoc_semiring α

-- We defer the instance `non_unital_non_assoc_ring.to_has_distrib_neg` to `algebra.ring.basic`
-- as it relies on the lemma `eq_neg_of_add_eq_zero_left`.

/-- An associative but not-necessarily unital ring. -/
@[protect_proj, ancestor non_unital_non_assoc_ring non_unital_semiring]
class non_unital_ring (α : Type*) extends
  non_unital_non_assoc_ring α, non_unital_semiring α

/-- A unital but not-necessarily-associative ring. -/
@[protect_proj, ancestor non_unital_non_assoc_ring non_assoc_semiring]
class non_assoc_ring (α : Type*) extends
  non_unital_non_assoc_ring α, non_assoc_semiring α, add_group_with_one α

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj, ancestor add_comm_group monoid distrib]
class ring (α : Type u) extends add_comm_group_with_one α, monoid α, distrib α

section non_unital_non_assoc_ring
variables [non_unital_non_assoc_ring α]

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


section non_assoc_ring
variables [non_assoc_ring α]

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

/- A (unital, associative) ring is a not-necessarily-unital ring -/
@[priority 100] -- see Note [lower instance priority]
instance ring.to_non_unital_ring :
  non_unital_ring α :=
{ zero_mul := λ a, add_left_cancel $ show 0 * a + 0 * a = 0 * a + 0,
    by rw [← add_mul, zero_add, add_zero],
  mul_zero := λ a, add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
    by rw [← mul_add, add_zero, add_zero],
  ..‹ring α› }

/- A (unital, associative) ring is a not-necessarily-associative ring -/
@[priority 100] -- see Note [lower instance priority]
instance ring.to_non_assoc_ring :
  non_assoc_ring α :=
{ zero_mul := λ a, add_left_cancel $ show 0 * a + 0 * a = 0 * a + 0,
    by rw [← add_mul, zero_add, add_zero],
  mul_zero := λ a, add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
    by rw [← mul_add, add_zero, add_zero],
  ..‹ring α› }

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
@[priority 200]
instance ring.to_semiring : semiring α :=
{ ..‹ring α›, .. ring.to_non_unital_ring }

end ring

/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj, ancestor non_unital_ring comm_semigroup]
class non_unital_comm_ring (α : Type u) extends non_unital_ring α, comm_semigroup α

@[priority 100] -- see Note [lower instance priority]
instance non_unital_comm_ring.to_non_unital_comm_semiring [s : non_unital_comm_ring α] :
  non_unital_comm_semiring α :=
{ ..s }

/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj, ancestor ring comm_semigroup]
class comm_ring (α : Type u) extends ring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

@[priority 100] -- see Note [lower instance priority]
instance comm_ring.to_non_unital_comm_ring [s : comm_ring α] : non_unital_comm_ring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

/-- A domain is a nontrivial semiring such multiplication by a non zero element is cancellative,
  on both sides. In other words, a nontrivial semiring `R` satisfying
  `∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
  `∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

  This is implemented as a mixin for `semiring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj, ancestor is_cancel_mul_zero nontrivial]
class is_domain (α : Type u) [semiring α] extends is_cancel_mul_zero α, nontrivial α : Prop
