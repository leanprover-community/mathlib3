/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

/-!
# Structure instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals from `0` to `1`.
-/

open set

/-- Instances for `(Icc 0 1)` -/

instance {α : Type*} [ordered_semiring α] : has_zero (Icc (0:α) 1) :=
  { zero := ⟨0, left_mem_Icc.2 zero_le_one⟩ }

instance {α : Type*} [ordered_semiring α] : has_one (Icc (0:α) 1) :=
  { one := ⟨1, right_mem_Icc.2 zero_le_one⟩ }

instance {α : Type*} [ordered_semiring α] : has_mul (Icc (0:α) 1) :=
  { mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩ }

instance {α : Type*} [ordered_semiring α] : has_pow (Icc (0:α) 1) ℕ :=
  { pow := λ p n, ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩ }

instance {α : Type*} [ordered_semiring α] : monoid (Icc (0:α) 1) :=
by { apply function.injective.monoid _ subtype.coe_injective; { intros, refl } }

instance {α : Type*} [ordered_comm_semiring α] : comm_monoid_with_zero (Icc (0:α) 1) :=
begin
  apply function.injective.comm_monoid_with_zero (λ (p:(Icc (0:α) 1)), p.1) subtype.coe_injective,
  { simp [has_zero.zero] },
  { simp [has_one.one] },
  { simp [has_mul.mul] },
  { simp only [has_pow.pow, subtype.coe_mk, eq_self_iff_true, forall_const] },
end

/-- Instances for `(Ico 0 1)` -/

instance {α : Type*} [ordered_semiring α] : semigroup (Ico (0:α) 1) :=
{ mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1,
    mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩,
  mul_assoc := λ p q r, (by exact subtype.mk_eq_mk.2 (mul_assoc p q r)) }

instance {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ico (0:α) 1) :=
{ mul_comm := λ ⟨p1, _⟩ ⟨q1, _⟩,
    (by {apply subtype.mk_eq_mk.2, simp [subtype.coe_mk, mul_comm p1 q1]}),
  ..(show semigroup (Ico (0:α) 1), by apply_instance) }

/-- Instances for `(Ioc 0 1)` -/

instance {α : Type*} [ordered_semiring α] [nontrivial α] : monoid (Ioc (0:α) 1) :=
{ mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩,
  mul_assoc := λ p q r, (by simp only [subtype.mk_eq_mk, mul_assoc]),
  one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩,
  one_mul := (by simp),
  mul_one := (by simp),
  npow := λ n p, ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩,
  npow_zero' := λ p, (by {simp only [pow_zero], refl}),
  npow_succ' := λ n ⟨p1, _⟩, (by {simp only [pow_succ p1 n], refl }) }

instance {α : Type*} [ordered_comm_semiring α] [nontrivial α] : comm_monoid (Ioc (0:α) 1) :=
{ mul_comm := λ p q, (by {ext1, exact mul_comm p.1 q.1}),
  ..(show monoid (Ioc (0:α) 1), by apply_instance) }

/-- Instances for `(Ioo 0 1)` -/

instance {α : Type*} [ordered_semiring α] : semigroup (Ioo (0:α) 1) :=
{ mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1,
    mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩,
  mul_assoc := λ p q r, (by simp only [subtype.mk_eq_mk, mul_assoc]) }

instance {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ioo (0:α) 1) :=
{ mul_comm := λ ⟨p1, _⟩ ⟨q1, _⟩,
    (by {apply subtype.mk_eq_mk.2, simp [subtype.coe_mk, mul_comm p1 q1]}),
  ..(show semigroup (Ioo (0:α) 1), by apply_instance) }
