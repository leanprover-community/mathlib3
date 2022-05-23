/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies
-/
import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`set.Icc`, `set.Ioc`, `set.Ioc`, and `set.Ioo`) from `0` to `1`.

Note: Instances for the interval `Ici 0` are dealt with in `algebra/order/nonneg.lean`.

## Main definitions
The strongest typeclass provided on each interval is:
* `set.Icc.cancel_comm_monoid_with_zero`
* `set.Ico.comm_semigroup`
* `set.Ioc.comm_monoid`
* `set.Ioo.comm_semigroup`

## TODO
* algebraic instances for intervals -1 to 1
* algebraic instances for `Ici 1`
* algebraic instances for `(Ioo (-1) 1)ᶜ`
* provide `has_distrib_neg` instances where applicable
* Can we prove `set.Ioc.cancel_comm_monoid` for `is_domain α`?

-/

variables {α : Type*} [ordered_semiring α]

open set

/-! ### Instances for `↥(set.Icc 0 1)` -/

namespace set.Icc

instance has_zero : has_zero (Icc (0:α) 1) := { zero := ⟨0, left_mem_Icc.2 zero_le_one⟩ }

instance has_one : has_one (Icc (0:α) 1) := { one := ⟨1, right_mem_Icc.2 zero_le_one⟩ }

instance has_mul : has_mul (Icc (0:α) 1) :=
{ mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩ }

instance has_pow : has_pow (Icc (0:α) 1) ℕ :=
{ pow := λ p n, ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_zero : ↑(0 : Icc (0:α) 1) = (0 : α) := rfl
@[simp, norm_cast] lemma coe_one : ↑(1 : Icc (0:α) 1) = (1 : α) := rfl
@[simp, norm_cast] lemma coe_mul (x y : Icc (0:α) 1) : ↑(x * y) = (x * y : α) := rfl
@[simp, norm_cast] lemma coe_pow (x : Icc (0:α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) := rfl

instance monoid_with_zero : monoid_with_zero (Icc (0:α) 1) :=
subtype.coe_injective.monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

instance comm_monoid_with_zero {α : Type*} [ordered_comm_semiring α] :
  comm_monoid_with_zero (Icc (0:α) 1) :=
subtype.coe_injective.comm_monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

instance cancel_monoid_with_zero {α : Type*} [ordered_ring α] [no_zero_divisors α] :
  cancel_monoid_with_zero (Icc (0:α) 1) :=
@function.injective.cancel_monoid_with_zero α _ no_zero_divisors.to_cancel_monoid_with_zero
  _ _ _ _ coe subtype.coe_injective coe_zero coe_one coe_mul coe_pow

-- TODO: tidy up after #14302
instance cancel_comm_monoid_with_zero {α : Type*} [ordered_comm_ring α] [no_zero_divisors α] :
  cancel_comm_monoid_with_zero (Icc (0:α) 1) :=
@function.injective.cancel_comm_monoid_with_zero α _
  { mul_comm := mul_comm, ..no_zero_divisors.to_cancel_monoid_with_zero }
  _ _ _ _ coe subtype.coe_injective coe_zero coe_one coe_mul coe_pow

end set.Icc

/-! ### Instances for `↥(set.Ico 0 1)` -/

namespace set.Ico

instance has_mul : has_mul (Ico (0:α) 1) :=
{ mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1,
  mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Ico (0:α) 1) : ↑(x * y) = (x * y : α) := rfl

instance semigroup : semigroup (Ico (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance comm_semigroup {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ico (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

end set.Ico

/-! ### Instances for `↥(set.Ioc 0 1)` -/

namespace set.Ioc

instance has_one [nontrivial α] : has_one (Ioc (0:α) 1) := { one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩ }

instance has_mul : has_mul (Ioc (0:α) 1) :=
{ mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩ }

instance has_pow : has_pow (Ioc (0:α) 1) ℕ :=
{ pow := λ p n, ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_one [nontrivial α] : ↑(1 : Ioc (0:α) 1) = (1 : α) := rfl
@[simp, norm_cast] lemma coe_mul (x y : Ioc (0:α) 1) : ↑(x * y) = (x * y : α) := rfl
@[simp, norm_cast] lemma coe_pow (x : Ioc (0:α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) := rfl

instance semigroup : semigroup (Ioc (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance monoid [nontrivial α] : monoid (Ioc (0:α) 1) :=
subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

instance comm_semigroup {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ioc (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

instance comm_monoid {α : Type*} [ordered_comm_semiring α] [nontrivial α] :
  comm_monoid (Ioc (0:α) 1) :=
subtype.coe_injective.comm_monoid _ coe_one coe_mul coe_pow

end set.Ioc

/-! ### Instances for `↥(set.Ioo 0 1)` -/

namespace set.Ioo

instance has_mul : has_mul (Ioo (0:α) 1) := { mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1,
  mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Ioo (0:α) 1) : ↑(x * y) = (x * y : α) := rfl

instance semigroup : semigroup (Ioo (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance comm_semigroup {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ioo (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

end set.Ioo
