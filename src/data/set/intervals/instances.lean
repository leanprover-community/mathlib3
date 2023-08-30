/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Scott Morrison
-/
import algebra.group_power.order
import algebra.ring.regular

/-!
# Algebraic instances for unit intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
* prove versions of `mul_le_{left,right}` for other intervals
* prove versions of the lemmas in `topology/unit_interval` with `ℝ` generalized to
  some arbitrary ordered semiring

-/

open set

variables {α : Type*}

section ordered_semiring
variables [ordered_semiring α]

/-! ### Instances for `↥(set.Icc 0 1)` -/

namespace set.Icc

instance has_zero : has_zero (Icc (0:α) 1) := { zero := ⟨0, left_mem_Icc.2 zero_le_one⟩ }

instance has_one : has_one (Icc (0:α) 1) := { one := ⟨1, right_mem_Icc.2 zero_le_one⟩ }

@[simp, norm_cast] lemma coe_zero : ↑(0 : Icc (0:α) 1) = (0 : α) := rfl
@[simp, norm_cast] lemma coe_one : ↑(1 : Icc (0:α) 1) = (1 : α) := rfl

@[simp] lemma mk_zero (h : (0 : α) ∈ Icc (0 : α) 1) : (⟨0, h⟩ : Icc (0:α) 1) = 0 := rfl
@[simp] lemma mk_one (h : (1 : α) ∈ Icc (0 : α) 1) : (⟨1, h⟩ : Icc (0:α) 1) = 1 := rfl

@[simp, norm_cast] lemma coe_eq_zero {x : Icc (0:α) 1} : (x : α) = 0 ↔ x = 0 :=
by { symmetry, exact subtype.ext_iff }

lemma coe_ne_zero {x : Icc (0:α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr coe_eq_zero

@[simp, norm_cast] lemma coe_eq_one {x : Icc (0:α) 1} : (x : α) = 1 ↔ x = 1 :=
by { symmetry, exact subtype.ext_iff }

lemma coe_ne_one {x : Icc (0:α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
not_iff_not.mpr coe_eq_one

lemma coe_nonneg (x : Icc (0:α) 1) : 0 ≤ (x : α) := x.2.1
lemma coe_le_one (x : Icc (0:α) 1) : (x : α) ≤ 1 := x.2.2

/-- like `coe_nonneg`, but with the inequality in `Icc (0:α) 1`. -/
lemma nonneg {t : Icc (0:α) 1} : 0 ≤ t := t.2.1
/-- like `coe_le_one`, but with the inequality in `Icc (0:α) 1`. -/
lemma le_one {t : Icc (0:α) 1} : t ≤ 1 := t.2.2

instance has_mul : has_mul (Icc (0:α) 1) :=
{ mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩ }

instance has_pow : has_pow (Icc (0:α) 1) ℕ :=
{ pow := λ p n, ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Icc (0:α) 1) : ↑(x * y) = (x * y : α) := rfl
@[simp, norm_cast] lemma coe_pow (x : Icc (0:α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) := rfl

lemma mul_le_left {x y : Icc (0:α) 1} : x * y ≤ x :=
(mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one x)

lemma mul_le_right {x y : Icc (0:α) 1} : x * y ≤ y :=
(mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul y)

instance monoid_with_zero : monoid_with_zero (Icc (0:α) 1) :=
subtype.coe_injective.monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

instance comm_monoid_with_zero {α : Type*} [ordered_comm_semiring α] :
  comm_monoid_with_zero (Icc (0:α) 1) :=
subtype.coe_injective.comm_monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

instance cancel_monoid_with_zero {α : Type*} [ordered_ring α] [no_zero_divisors α] :
  cancel_monoid_with_zero (Icc (0:α) 1) :=
@function.injective.cancel_monoid_with_zero α _ no_zero_divisors.to_cancel_monoid_with_zero
  _ _ _ _ coe subtype.coe_injective coe_zero coe_one coe_mul coe_pow

instance cancel_comm_monoid_with_zero {α : Type*} [ordered_comm_ring α] [no_zero_divisors α] :
  cancel_comm_monoid_with_zero (Icc (0:α) 1) :=
@function.injective.cancel_comm_monoid_with_zero α _
  no_zero_divisors.to_cancel_comm_monoid_with_zero
  _ _ _ _ coe subtype.coe_injective coe_zero coe_one coe_mul coe_pow

variables {β : Type*} [ordered_ring β]

lemma one_sub_mem {t : β} (ht : t ∈ Icc (0:β) 1) : 1 - t ∈ Icc (0:β) 1 :=
by { rw mem_Icc at *, exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩ }

lemma mem_iff_one_sub_mem {t : β} : t ∈ Icc (0:β) 1 ↔ 1 - t ∈ Icc (0:β) 1 :=
⟨one_sub_mem, λ h, (sub_sub_cancel 1 t) ▸ one_sub_mem h⟩

lemma one_sub_nonneg (x : Icc (0:β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2
lemma one_sub_le_one (x : Icc (0:β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1

end set.Icc

/-! ### Instances for `↥(set.Ico 0 1)` -/

namespace set.Ico

instance has_zero [nontrivial α] : has_zero (Ico (0:α) 1) :=
  { zero := ⟨0, left_mem_Ico.2 zero_lt_one⟩ }

@[simp, norm_cast] lemma coe_zero [nontrivial α] : ↑(0 : Ico (0:α) 1) = (0 : α) := rfl

@[simp] lemma mk_zero [nontrivial α] (h : (0 : α) ∈ Ico (0 : α) 1) : (⟨0, h⟩ : Ico (0:α) 1) = 0 :=
  rfl

@[simp, norm_cast] lemma coe_eq_zero [nontrivial α] {x : Ico (0:α) 1} : (x : α) = 0 ↔ x = 0 :=
by { symmetry, exact subtype.ext_iff }

lemma coe_ne_zero [nontrivial α] {x : Ico (0:α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr coe_eq_zero

lemma coe_nonneg (x : Ico (0:α) 1) : 0 ≤ (x : α) := x.2.1
lemma coe_lt_one (x : Ico (0:α) 1) : (x : α) < 1 := x.2.2

/-- like `coe_nonneg`, but with the inequality in `Ico (0:α) 1`. -/
lemma nonneg [nontrivial α] {t : Ico (0:α) 1} : 0 ≤ t := t.2.1

instance has_mul : has_mul (Ico (0:α) 1) :=
{ mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1,
  mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Ico (0:α) 1) : ↑(x * y) = (x * y : α) := rfl

instance semigroup : semigroup (Ico (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance comm_semigroup {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ico (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

end set.Ico

end ordered_semiring

variables [strict_ordered_semiring α]

/-! ### Instances for `↥(set.Ioc 0 1)` -/

namespace set.Ioc

instance has_one [nontrivial α] : has_one (Ioc (0:α) 1) := { one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩ }

@[simp, norm_cast] lemma coe_one [nontrivial α] : ↑(1 : Ioc (0:α) 1) = (1 : α) := rfl

@[simp] lemma mk_one [nontrivial α] (h : (1 : α) ∈ Ioc (0 : α) 1) : (⟨1, h⟩ : Ioc (0:α) 1) = 1 :=
  rfl

@[simp, norm_cast] lemma coe_eq_one [nontrivial α] {x : Ioc (0:α) 1} : (x : α) = 1 ↔ x = 1 :=
by { symmetry, exact subtype.ext_iff }

lemma coe_ne_one [nontrivial α] {x : Ioc (0:α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
not_iff_not.mpr coe_eq_one

lemma coe_pos (x : Ioc (0:α) 1) : 0 < (x : α) := x.2.1
lemma coe_le_one (x : Ioc (0:α) 1) : (x : α) ≤ 1 := x.2.2

/-- like `coe_le_one`, but with the inequality in `Ioc (0:α) 1`. -/
lemma le_one [nontrivial α] {t : Ioc (0:α) 1} : t ≤ 1 := t.2.2

instance has_mul : has_mul (Ioc (0:α) 1) :=
{ mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩ }

instance has_pow : has_pow (Ioc (0:α) 1) ℕ :=
{ pow := λ p n, ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Ioc (0:α) 1) : ↑(x * y) = (x * y : α) := rfl
@[simp, norm_cast] lemma coe_pow (x : Ioc (0:α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) := rfl

instance semigroup : semigroup (Ioc (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance monoid [nontrivial α] : monoid (Ioc (0:α) 1) :=
subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

instance comm_semigroup {α : Type*} [strict_ordered_comm_semiring α] :
  comm_semigroup (Ioc (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

instance comm_monoid {α : Type*} [strict_ordered_comm_semiring α] [nontrivial α] :
  comm_monoid (Ioc (0:α) 1) :=
subtype.coe_injective.comm_monoid _ coe_one coe_mul coe_pow

instance cancel_monoid {α : Type*} [strict_ordered_ring α] [is_domain α] :
  cancel_monoid (Ioc (0:α) 1) :=
{ mul_left_cancel := λ a b c h,
    subtype.ext $ mul_left_cancel₀ a.prop.1.ne' $ (congr_arg subtype.val h : _),
  mul_right_cancel := λ a b c h,
    subtype.ext $ mul_right_cancel₀ b.prop.1.ne' $ (congr_arg subtype.val h : _),
  ..set.Ioc.monoid}

instance cancel_comm_monoid {α : Type*} [strict_ordered_comm_ring α] [is_domain α] :
  cancel_comm_monoid (Ioc (0:α) 1) :=
{ ..set.Ioc.cancel_monoid, ..set.Ioc.comm_monoid }

end set.Ioc

/-! ### Instances for `↥(set.Ioo 0 1)` -/

namespace set.Ioo

lemma pos (x : Ioo (0:α) 1) : 0 < (x : α) := x.2.1
lemma lt_one (x : Ioo (0:α) 1) : (x : α) < 1 := x.2.2

instance has_mul : has_mul (Ioo (0:α) 1) := { mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1,
  mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩ }

@[simp, norm_cast] lemma coe_mul (x y : Ioo (0:α) 1) : ↑(x * y) = (x * y : α) := rfl

instance semigroup : semigroup (Ioo (0:α) 1) :=
subtype.coe_injective.semigroup _ coe_mul

instance comm_semigroup {α : Type*} [strict_ordered_comm_semiring α] :
  comm_semigroup (Ioo (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

variables {β : Type*} [ordered_ring β]

lemma one_sub_mem {t : β} (ht : t ∈ Ioo (0:β) 1) : 1 - t ∈ Ioo (0:β) 1 :=
begin
  rw mem_Ioo at *,
  refine ⟨sub_pos.2 ht.2, _⟩,
  exact lt_of_le_of_ne ((sub_le_self_iff 1).2 ht.1.le) (mt sub_eq_self.mp ht.1.ne'),
end

lemma mem_iff_one_sub_mem {t : β} : t ∈ Ioo (0:β) 1 ↔ 1 - t ∈ Ioo (0:β) 1 :=
⟨one_sub_mem, λ h, (sub_sub_cancel 1 t) ▸ one_sub_mem h⟩

lemma one_minus_pos (x : Ioo (0:β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2
lemma one_minus_lt_one (x : Ioo (0:β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

end set.Ioo
