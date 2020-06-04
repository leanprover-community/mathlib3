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

@[simp] lemma pow_right {a x y : M} (h : semiconj_by a x y) :
  ∀ n : ℕ, semiconj_by a (x^n) (y^n)
| 0 := one_right a
| (n+1) := by simp only [pow_succ, h, pow_right n, mul_right]

@[simp] lemma units_gpow_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (↑(x^m)) (↑(y^m))
| (n : ℕ) := by simp only [gpow_coe_nat, units.coe_pow, h, pow_right]
| -[1+n] := by simp only [gpow_neg_succ, units.coe_pow, units_inv_right, h, pow_right]

@[simp] lemma gpow_right (h : semiconj_by a x y) : ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := h.pow_right n
| -[1+n] := (h.pow_right n.succ).inv_right

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
