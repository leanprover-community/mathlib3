/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.order
/-!
# Floor and Ceil Functions for Rational Numbers

## Summary

We define the `floor`, `ceil`, and `nat_ceil` functions on `ℚ`.

## Main Definitions

- `floor q` is the largest integer `z` such that `z ≤ q`.
- `ceil q` is the smallest integer `z` such that `q ≤ z` .
- `nat_ceil q` is the smallest nonnegative integer `n` with `q ≤ n`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, ceil, floor
-/

namespace rat

section floor

/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ := n / d

lemma floor_def {q : ℚ} : floor q = q.num / q.denom := by { cases q, refl }

theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ floor r ↔ (z : ℚ) ≤ r
| ⟨n, d, h, c⟩ := begin
  simp [floor],
  rw [num_denom'],
  have h' := int.coe_nat_lt.2 h,
  conv { to_rhs,
    rw [coe_int_eq_mk, mk_le zero_lt_one h', mul_one] },
  exact int.le_div_iff_mul_le h'
end

theorem floor_lt {r : ℚ} {z : ℤ} : floor r < z ↔ r < z :=
lt_iff_lt_of_le_iff_le le_floor

theorem floor_le (r : ℚ) : (floor r : ℚ) ≤ r :=
le_floor.1 (le_refl _)

theorem lt_succ_floor (r : ℚ) : r < (floor r).succ :=
floor_lt.1 $ int.lt_succ_self _

@[simp] theorem floor_coe (z : ℤ) : floor z = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

theorem floor_mono {a b : ℚ} (h : a ≤ b) : floor a ≤ floor b :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (r : ℚ) (z : ℤ) : floor (r + z) = floor r + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (r : ℚ) (z : ℤ) : floor (r - z) = floor r - z :=
eq.trans (by rw [int.cast_neg]; refl) (floor_add_int _ _)

end floor

section ceil

/-- `ceil q` is the smallest integer `z` such that `q ≤ z` -/
def ceil (r : ℚ) : ℤ :=
-(floor (-r))

theorem ceil_le {z : ℤ} {r : ℚ} : ceil r ≤ z ↔ r ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem le_ceil (r : ℚ) : r ≤ ceil r :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ceil z = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : ℚ} (h : a ≤ b) : ceil a ≤ ceil b :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (r : ℚ) (z : ℤ) : ceil (r + z) = ceil r + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (r : ℚ) (z : ℤ) : ceil (r - z) = ceil r - z :=
eq.trans (by rw [int.cast_neg]; refl) (ceil_add_int _ _)

end ceil

section nat_ceil

/-- `nat_ceil q` is the smallest nonnegative integer `n` with `q ≤ n`.
  It is the same as `ceil q` when `q ≥ 0`, otherwise it is `0`. -/
def nat_ceil (q : ℚ) : ℕ := int.to_nat (ceil q)

theorem nat_ceil_le {q : ℚ} {n : ℕ} : nat_ceil q ≤ n ↔ q ≤ n :=
by rw [nat_ceil, int.to_nat_le, ceil_le]; refl

theorem lt_nat_ceil {q : ℚ} {n : ℕ} : n < nat_ceil q ↔ (n : ℚ) < q :=
not_iff_not.1 $ by rw [not_lt, not_lt, nat_ceil_le]

theorem le_nat_ceil (q : ℚ) : q ≤ nat_ceil q :=
nat_ceil_le.1 (le_refl _)

theorem nat_ceil_mono {q₁ q₂ : ℚ} (h : q₁ ≤ q₂) : nat_ceil q₁ ≤ nat_ceil q₂ :=
nat_ceil_le.2 (le_trans h (le_nat_ceil _))

@[simp] theorem nat_ceil_coe (n : ℕ) : nat_ceil n = n :=
show (ceil (n:ℤ)).to_nat = n, by rw [ceil_coe]; refl

@[simp] theorem nat_ceil_zero : nat_ceil 0 = 0 := nat_ceil_coe 0

theorem nat_ceil_add_nat {q : ℚ} (hq : 0 ≤ q) (n : ℕ) : nat_ceil (q + n) = nat_ceil q + n :=
show int.to_nat (ceil (q + (n:ℤ))) = int.to_nat (ceil q) + n,
by rw [ceil_add_int]; exact
match ceil q, int.eq_coe_of_zero_le (ceil_mono hq) with
| _, ⟨m, rfl⟩ := rfl
end

theorem nat_ceil_lt_add_one {q : ℚ} (hq : q ≥ 0) : ↑(nat_ceil q) < q + 1 :=
lt_nat_ceil.1 $ by rw [
  show nat_ceil (q+1) = nat_ceil q+1, from nat_ceil_add_nat hq 1]; apply nat.lt_succ_self

end nat_ceil
end rat
