/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import algebra.group_power
import data.equiv.mul_add

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument,
and both `x` and `y` as “right” arguments. This way most names in this
file agree with the names of the corresponding lemmas for `commute a b
= semiconj_by a b b`. As a side effect, some lemmas have only `_right`
version.

Lean does not immediately recognise these terms as equations,
so for rewriting we need syntax like `rw [(h.pow_right 5).eq]`
rather than just `rw [h.pow_right 5]`.
-/

universes u v

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
def semiconj_by {M : Type u} [has_mul M] (a x y : M) : Prop := a * x = y * a

namespace semiconj_by

/-- Equality behind `semiconj_by a x y`; useful for rewriting. -/
protected lemma eq {S : Type u} [has_mul S] {a x y : S} (h : semiconj_by a x y) :
  a * x = y * a := h

section semigroup

variables {S : Type u} [semigroup S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[simp] lemma mul_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x * x') (y * y') :=
by unfold semiconj_by; assoc_rw [h.eq, h'.eq]

/-- If both `a` and `b` semiconjugate `x` to `y`, then so does `a * b`. -/
lemma mul_left (ha : semiconj_by a y z) (hb : semiconj_by b x y) :
  semiconj_by (a * b) x z :=
by unfold semiconj_by; assoc_rw [hb.eq, ha.eq, mul_assoc]

end semigroup

section monoid

variables {M : Type u} [monoid M]

/-- Any element semiconjugates `1` to `1`. -/
@[simp] lemma one_right (a : M) : semiconj_by a 1 1 := by rw [semiconj_by, mul_one, one_mul]

/-- One semiconjugates any element to itself. -/
@[simp] lemma one_left (x : M) : semiconj_by 1 x x := eq.symm $ one_right x

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
lemma units_inv_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  semiconj_by a ↑x⁻¹ ↑y⁻¹ :=
calc a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ : by rw [units.inv_mul_cancel_left]
          ... = ↑y⁻¹ * a              : by rw [← h.eq, mul_assoc, units.mul_inv_cancel_right]

@[simp] lemma units_inv_right_iff {a : M} {x y : units M} :
  semiconj_by a ↑x⁻¹ ↑y⁻¹ ↔ semiconj_by a x y :=
⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
lemma units_inv_symm_left {a : units M} {x y : M} (h : semiconj_by ↑a x y) :
  semiconj_by ↑a⁻¹ y x :=
calc ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) : by rw [units.mul_inv_cancel_right]
          ... = x * ↑a⁻¹              : by rw [← h.eq, ← mul_assoc, units.inv_mul_cancel_left]

@[simp] lemma units_inv_symm_left_iff {a : units M} {x y : M} :
  semiconj_by ↑a⁻¹ y x ↔ semiconj_by ↑a x y :=
⟨units_inv_symm_left, units_inv_symm_left⟩

@[simp] protected lemma map {N : Type v} [monoid N] (f : M →* N) {a x y : M} (h : semiconj_by a x y) :
  semiconj_by (f a) (f x) (f y) :=
by simpa only [semiconj_by, f.map_mul] using congr_arg f h

theorem units_coe {a x y : units M} (h : semiconj_by a x y) :
  semiconj_by (a : M) x y :=
congr_arg units.val h

theorem units_of_coe {a x y : units M} (h : semiconj_by (a : M) x y) :
  semiconj_by a x y :=
units.ext h

@[simp] theorem units_coe_iff {a x y : units M} :
  semiconj_by (a : M) x y ↔ semiconj_by a x y :=
⟨units_of_coe, units_coe⟩

@[simp] lemma pow_right {a x y : M} (h : semiconj_by a x y) :
  ∀ n : ℕ, semiconj_by a (x^n) (y^n)
| 0 := one_right a
| (n+1) := by simp only [pow_succ, h, pow_right n, mul_right]

@[simp] lemma units_gpow_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (↑(x^m)) (↑(y^m))
| (n : ℕ) := by simp only [gpow_coe_nat, units.coe_pow, h, pow_right]
| -[1+n] := by simp only [gpow_neg_succ, units.coe_pow, units_inv_right, h, pow_right]

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
lemma units_conj_mk (a : units M) (x : M) : semiconj_by ↑a x (a * x * ↑a⁻¹) :=
by unfold semiconj_by; rw [units.inv_mul_cancel_right]

end monoid

section group

variables {G : Type u} [group G] {a x y : G}

@[simp] lemma inv_right_iff : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
@units_inv_right_iff G _ a (to_units G x) (to_units G y)

lemma inv_right : semiconj_by a x y → semiconj_by a x⁻¹ y⁻¹ :=
inv_right_iff.2

@[simp] lemma inv_symm_left_iff : semiconj_by a⁻¹ y x ↔ semiconj_by a x y :=
@units_inv_symm_left_iff G _ (to_units G a) _ _

lemma inv_symm_left : semiconj_by a x y → semiconj_by a⁻¹ y x :=
inv_symm_left_iff.2

lemma inv_inv_symm (h : semiconj_by a x y) : semiconj_by a⁻¹ y⁻¹ x⁻¹ :=
h.inv_right.inv_symm_left

lemma inv_inv_symm_iff : semiconj_by a⁻¹ y⁻¹ x⁻¹ ↔ semiconj_by a x y :=
inv_right_iff.trans inv_symm_left_iff

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
lemma conj_mk (a x : G) : semiconj_by a x (a * x * a⁻¹) :=
by unfold semiconj_by; rw [inv_mul_cancel_right]

@[simp] lemma gpow_right (h : semiconj_by a x y) : ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := h.pow_right n
| -[1+n] := (h.pow_right n.succ).inv_right

end group

section semiring

variables {R : Type u}

@[simp] lemma add_right [distrib R] {a x y x' y' : R}
  (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x + x') (y + y') :=
by simp only [semiconj_by, left_distrib, right_distrib, h.eq, h'.eq]

@[simp] lemma add_left [distrib R] {a b x y : R}
  (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a + b) x y :=
by simp only [semiconj_by, left_distrib, right_distrib, ha.eq, hb.eq]

@[simp] lemma zero_right [mul_zero_class R] (a : R) : semiconj_by a 0 0 :=
by simp only [semiconj_by, mul_zero, zero_mul]

@[simp] lemma zero_left [mul_zero_class R] (x y : R) : semiconj_by 0 x y :=
by simp only [semiconj_by, mul_zero, zero_mul]

variables [semiring R] {a b x y : R} (h : semiconj_by a x y)
include h

@[simp] lemma nsmul_right : ∀ n, semiconj_by a (n •ℕ x) (n •ℕ y)
| 0 := zero_right a
| (n+1) := by simp only [succ_nsmul]; exact h.add_right (nsmul_right n)

@[simp] lemma nsmul_left : ∀ n, semiconj_by (n •ℕ a) x y
| 0 := zero_left x y
| (n+1) := by simp only [succ_nsmul]; exact h.add_left (nsmul_left n)

lemma nsmul_nsmul (m n : ℕ) : semiconj_by (m •ℕ a) (n •ℕ x) (n •ℕ y) :=
(h.nsmul_left m).nsmul_right n

omit h

lemma cast_nat_right (a : R) (n : ℕ) : semiconj_by a n n :=
by rw [← nsmul_one n]; exact (one_right a).nsmul_right n

lemma cast_nat_left (n : ℕ) (x : R) : semiconj_by (n : R) x x :=
by rw [← nsmul_one n]; exact (one_left x).nsmul_left n

end semiring

section ring

variables {R : Type u} [ring R] {a b x y x' y' : R}

lemma neg_right (h : semiconj_by a x y) : semiconj_by a (-x) (-y) :=
by simp only [semiconj_by, h.eq, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm]

@[simp] lemma neg_right_iff : semiconj_by a (-x) (-y) ↔ semiconj_by a x y :=
⟨λ h, neg_neg x ▸ neg_neg y ▸ h.neg_right, neg_right⟩

lemma neg_left (h : semiconj_by a x y) : semiconj_by (-a) x y :=
by simp only [semiconj_by, h.eq, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm]

@[simp] lemma neg_left_iff : semiconj_by (-a) x y ↔ semiconj_by a x y :=
⟨λ h, neg_neg a ▸ h.neg_left, neg_left⟩

@[simp] lemma neg_one_right (a : R) : semiconj_by a (-1) (-1) :=
(one_right a).neg_right

@[simp] lemma neg_one_left (x : R) : semiconj_by (-1) x x :=
(one_left x).neg_left

@[simp] lemma sub_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x - x') (y - y') :=
h.add_right h'.neg_right

@[simp] lemma sub_left (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a - b) x y :=
ha.add_left hb.neg_left

@[simp] lemma gsmul_right (h : semiconj_by a x y) : ∀ m, semiconj_by a (m •ℤ x) (m •ℤ y)
| (n : ℕ) := h.nsmul_right n
| -[1+n] := (h.nsmul_right n.succ).neg_right

@[simp] lemma gsmul_left (h : semiconj_by a x y) : ∀ m, semiconj_by (m •ℤ a) x y
| (n : ℕ) := h.nsmul_left n
| -[1+n] := (h.nsmul_left n.succ).neg_left

lemma gsmul_gsmul (h : semiconj_by a x y) (m n : ℤ) : semiconj_by (m •ℤ a) (n •ℤ x) (n •ℤ y) :=
(h.gsmul_left m).gsmul_right n

end ring

section division_ring

variables {R : Type*} [division_ring R] {a x y : R}

@[simp] lemma finv_symm_left_iff : semiconj_by a⁻¹ x y ↔ semiconj_by a y x :=
classical.by_cases
  (λ ha : a = 0, by simp only [ha, inv_zero, zero_left])
  (λ ha, @units_inv_symm_left_iff _ _ (units.mk0 a ha) _ _)

lemma finv_symm_left (h : semiconj_by a x y) : semiconj_by a⁻¹ y x :=
finv_symm_left_iff.2 h

end division_ring

end semiconj_by
