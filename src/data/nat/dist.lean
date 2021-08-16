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
by simp [dist.def, nat.sub_self]

theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m :=
have n - m = 0, from nat.eq_zero_of_add_eq_zero_right h,
have n ≤ m, from nat.le_of_sub_eq_zero this,
have m - n = 0, from nat.eq_zero_of_add_eq_zero_left h,
have m ≤ n, from nat.le_of_sub_eq_zero this,
le_antisymm ‹n ≤ m› ‹m ≤ n›

theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 :=
begin rw [h, dist_self] end

theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n :=
begin rw [dist.def, nat.sub_eq_zero_of_le h, zero_add] end

theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m :=
begin rw [dist_comm], apply dist_eq_sub_of_le h end

theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n :=
le_trans (nat.le_sub_add _ _) (add_le_add_right (nat.le_add_left _ _) _)

theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m :=
by rw add_comm; apply dist_tri_left

theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m :=
by rw dist_comm; apply dist_tri_left

theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m :=
by rw dist_comm; apply dist_tri_right

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
eq.trans (dist_eq_sub_of_le_right (zero_le n)) (nat.sub_zero n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
eq.trans (dist_eq_sub_of_le (zero_le n)) (nat.sub_zero n)

theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
calc
  dist (n + k) (m + k) = ((n + k) - (m + k)) + ((m + k)-(n + k)) : rfl
                   ... = (n - m) + ((m + k) - (n + k))   : by rw nat.add_sub_add_right
                   ... = (n - m) + (m - n)               : by rw nat.add_sub_add_right

theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m :=
begin rw [add_comm k n, add_comm k m], apply dist_add_add_right end

theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m :=
calc
  dist n k = dist (n + m) (k + m) : by rw dist_add_add_right
       ... = dist (k + l) (k + m) : by rw h
       ... = dist l m             : by rw dist_add_add_left

protected theorem sub_lt_sub_add_sub (n m k : ℕ) : n - k ≤ (n - m) + (m - k) :=
or.elim (le_total k m)
  (assume : k ≤ m,
    begin rw ←nat.add_sub_assoc this, apply nat.sub_le_sub_right, apply nat.le_sub_add end)
  (assume : k ≥ m,
    begin rw [nat.sub_eq_zero_of_le this, add_zero], apply nat.sub_le_sub_left, exact this end)

theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
have dist n m + dist m k = (n - m) + (m - k) + ((k - m) + (m - n)),
  by simp [dist.def, add_comm, add_left_comm],
begin
  rw [this, dist.def], apply add_le_add, repeat { apply nat.sub_lt_sub_add_sub }
end

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k :=
by rw [dist.def, dist.def, right_distrib, nat.mul_sub_right_distrib, nat.mul_sub_right_distrib]

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
     begin rw [dist_eq_sub_of_le (le_of_lt this)], apply nat.sub_pos_of_lt this end)
  (assume : i = j, by contradiction)
  (assume : i > j,
     begin rw [dist_eq_sub_of_le_right (le_of_lt this)], apply nat.sub_pos_of_lt this end)

end nat
