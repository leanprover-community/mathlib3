/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Scott Morrison
-/
import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

import topology.instances.real
import topology.algebra.field
import data.set.intervals.proj_Icc


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

instance cancel_comm_monoid_with_zero {α : Type*} [ordered_comm_ring α] [no_zero_divisors α] :
  cancel_comm_monoid_with_zero (Icc (0:α) 1) :=
@function.injective.cancel_comm_monoid_with_zero α _
  no_zero_divisors.to_cancel_comm_monoid_with_zero
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

instance cancel_monoid {α : Type*} [ordered_comm_ring α] [is_domain α] :
  cancel_monoid (Ioc (0:α) 1) :=
{ mul_left_cancel := λ a b c h,
    subtype.ext $ mul_left_cancel₀ a.prop.1.ne' $ (congr_arg subtype.val h : _),
  mul_right_cancel := λ a b c h,
    subtype.ext $ mul_right_cancel₀ b.prop.1.ne' $ (congr_arg subtype.val h : _),
  ..set.Ioc.monoid}

instance comm_semigroup {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ioc (0:α) 1) :=
subtype.coe_injective.comm_semigroup _ coe_mul

instance comm_monoid {α : Type*} [ordered_comm_semiring α] [nontrivial α] :
  comm_monoid (Ioc (0:α) 1) :=
subtype.coe_injective.comm_monoid _ coe_one coe_mul coe_pow

instance cancel_comm_monoid {α : Type*} [ordered_comm_ring α] [is_domain α] :
  cancel_comm_monoid (Ioc (0:α) 1) :=
{ ..set.Ioc.cancel_monoid, ..set.Ioc.comm_monoid }

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

/-! ### The unit interval in the real numbers

Use `open_locale unit_interval` to turn on the notation `I := set.Icc (0 : ℝ) (1 : ℝ)`.

-/

/-- The unit interval `[0,1]` in ℝ. -/
abbreviation unit_interval : set ℝ := set.Icc 0 1

localized "notation `I` := unit_interval" in unit_interval

namespace unit_interval

lemma zero_mem : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩

lemma one_mem : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩

lemma mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq $ one_mul 1⟩

lemma div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
⟨div_nonneg hx hy, div_le_one_of_le hxy hy⟩

lemma fract_mem (x : ℝ) : int.fract x ∈ I := ⟨int.fract_nonneg _, (int.fract_lt_one _).le⟩

lemma mem_iff_one_sub_mem {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

instance has_zero : has_zero I := ⟨⟨0, zero_mem⟩⟩

@[norm_cast] lemma coe_zero : ((0 : I) : ℝ) = 0 := rfl

@[simp] lemma mk_zero (h : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨0, h⟩ : I) = 0 := rfl

@[simp, norm_cast] lemma coe_eq_zero {x : I} : (x : ℝ) = 0 ↔ x = 0 :=
by { symmetry, exact subtype.ext_iff }

instance has_one : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

@[norm_cast] lemma coe_one : ((1 : I) : ℝ) = 1 := rfl

lemma coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr coe_eq_zero

@[simp] lemma mk_one (h : (1 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨1, h⟩ : I) = 1 := rfl

@[simp, norm_cast] lemma coe_eq_one {x : I} : (x : ℝ) = 1 ↔ x = 1 :=
by { symmetry, exact subtype.ext_iff }

lemma coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 :=
not_iff_not.mpr coe_eq_one

instance : nonempty I := ⟨0⟩

instance : has_mul I := ⟨λ x y, ⟨x * y, mul_mem x.2 y.2⟩⟩

@[norm_cast] lemma coe_mul {x y : I} : ((x * y : I) : ℝ) = x * y := rfl

-- todo: we could set up a `linear_ordered_comm_monoid_with_zero I` instance

lemma mul_le_left {x y : I} : x * y ≤ x :=
subtype.coe_le_coe.mp $ (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq $ mul_one x

lemma mul_le_right {x y : I} : x * y ≤ y :=
subtype.coe_le_coe.mp $ (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq $ one_mul y

/-- Unit interval central symmetry. -/
def symm : I → I := λ t, ⟨1 - t, mem_iff_one_sub_mem.mp t.prop⟩

localized "notation `σ` := unit_interval.symm" in unit_interval

@[simp] lemma symm_zero : σ 0 = 1 :=
by { simp only [symm], push_cast [sub_zero, mk_one] }

@[simp] lemma symm_one : σ 1 = 0 :=
by { simp only [symm], push_cast [sub_self, mk_zero] }

@[simp] lemma symm_symm (x : I) : σ (σ x) = x :=
subtype.ext $ by simp [symm]

@[simp] lemma coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x := rfl

lemma nonneg (x : I) : 0 ≤ (x : ℝ) := x.2.1
lemma one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
lemma le_one (x : I) : (x : ℝ) ≤ 1 := x.2.2
lemma one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1

/-- like `unit_interval.nonneg`, but with the inequality in `I`. -/
lemma nonneg' {t : I} : 0 ≤ t := t.2.1
/-- like `unit_interval.le_one`, but with the inequality in `I`. -/
lemma le_one' {t : I} : t ≤ 1 := t.2.2

lemma mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ set.Icc (0 : ℝ) (1/a) :=
begin
  split; rintros ⟨h₁, h₂⟩; split,
  { exact nonneg_of_mul_nonneg_left h₁ ha },
  { rwa [le_div_iff ha, mul_comm] },
  { exact mul_nonneg ha.le h₁ },
  { rwa [le_div_iff ha, mul_comm] at h₂ }
end

lemma two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ set.Icc (1/2 : ℝ) 1 :=
by split; rintros ⟨h₁, h₂⟩; split; linarith

end unit_interval

@[simp] lemma proj_Icc_eq_zero {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
proj_Icc_eq_left zero_lt_one

@[simp] lemma proj_Icc_eq_one {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
proj_Icc_eq_right zero_lt_one
