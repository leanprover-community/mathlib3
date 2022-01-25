/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad
-/
import data.nat.basic

/-!
#  Distance function on ℕ

This file defines a simple distance function on naturals from truncated substraction.
-/

namespace nat

/-- Distance (absolute value of difference) between natural numbers. -/
def dist (n m : ℕ) := (n - m) + (m - n)

theorem dist.def (n m : ℕ) : dist n m = (n - m) + (m - n) := rfl

theorem dist_comm (n m : ℕ) : dist n m = dist m n :=
by simp [dist.def, add_comm]

@[simp] theorem dist_self (n : ℕ) : dist n n = 0 :=
by simp [dist.def, tsub_self]

theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m :=
have n - m = 0, from nat.eq_zero_of_add_eq_zero_right h,
have n ≤ m, from tsub_eq_zero_iff_le.mp this,
have m - n = 0, from nat.eq_zero_of_add_eq_zero_left h,
have m ≤ n, from tsub_eq_zero_iff_le.mp this,
le_antisymm ‹n ≤ m› ‹m ≤ n›

theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 :=
begin rw [h, dist_self] end

theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n :=
begin rw [dist.def, tsub_eq_zero_iff_le.mpr h, zero_add] end

theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m :=
begin rw [dist_comm], apply dist_eq_sub_of_le h end

theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n :=
le_trans le_tsub_add (add_le_add_right (nat.le_add_left _ _) _)

theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m :=
by rw add_comm; apply dist_tri_left

theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m :=
by rw dist_comm; apply dist_tri_left

theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m :=
by rw dist_comm; apply dist_tri_right

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
eq.trans (dist_eq_sub_of_le_right (zero_le n)) (tsub_zero n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
eq.trans (dist_eq_sub_of_le (zero_le n)) (tsub_zero n)

theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
calc
  dist (n + k) (m + k) = ((n + k) - (m + k)) + ((m + k)-(n + k)) : rfl
                   ... = (n - m) + ((m + k) - (n + k))   : by rw add_tsub_add_eq_tsub_right
                   ... = (n - m) + (m - n)               : by rw add_tsub_add_eq_tsub_right

theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m :=
begin rw [add_comm k n, add_comm k m], apply dist_add_add_right end

theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m :=
calc
  dist n k = dist (n + m) (k + m) : by rw dist_add_add_right
       ... = dist (k + l) (k + m) : by rw h
       ... = dist l m             : by rw dist_add_add_left

theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
have dist n m + dist m k = (n - m) + (m - k) + ((k - m) + (m - n)),
  by simp [dist.def, add_comm, add_left_comm],
by { rw [this, dist.def], exact add_le_add tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub }

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k :=
by rw [dist.def, dist.def, right_distrib, tsub_mul, tsub_mul]

theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m :=
by rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]

-- TODO(Jeremy): do when we have max and minx
--theorem dist_eq_max_sub_min {i j : nat} : dist i j = (max i j) - min i j :=
--sorry
/-
or.elim (lt_or_ge i j)
  (assume : i < j,
    by rw [max_eq_right_of_lt this, min_eq_left_of_lt this, dist_eq_sub_of_lt this])
  (assume : i ≥ j,
    by rw [max_eq_left this , min_eq_right this, dist_eq_sub_of_le_right this])
-/

theorem dist_succ_succ {i j : nat} : dist (succ i) (succ j) = dist i j :=
by simp [dist.def, succ_sub_succ]

theorem dist_pos_of_ne {i j : nat} : i ≠ j → 0 < dist i j :=
assume hne, nat.lt_by_cases
  (assume : i < j,
     begin rw [dist_eq_sub_of_le (le_of_lt this)], apply tsub_pos_of_lt this end)
  (assume : i = j, by contradiction)
  (assume : i > j,
     begin rw [dist_eq_sub_of_le_right (le_of_lt this)], apply tsub_pos_of_lt this end)

end nat
