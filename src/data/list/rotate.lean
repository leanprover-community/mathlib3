/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.list.basic

universes u
variables {α : Type u}

open nat

namespace list

lemma rotate_mod (l : list α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n :=
by simp [rotate]

@[simp] lemma rotate_nil (n : ℕ) : ([] : list α).rotate n = [] := by cases n; refl

@[simp] lemma rotate_zero (l : list α) : l.rotate 0 = l := by simp [rotate]

@[simp] lemma rotate'_nil (n : ℕ) : ([] : list α).rotate' n = [] := by cases n; refl

@[simp] lemma rotate'_zero (l : list α) : l.rotate' 0 = l := by cases l; refl

lemma rotate'_cons_succ (l : list α) (a : α) (n : ℕ) :
  (a :: l : list α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp] lemma length_rotate' : ∀ (l : list α) (n : ℕ), (l.rotate' n).length = l.length
| []     n     := rfl
| (a::l) 0     := rfl
| (a::l) (n+1) := by rw [list.rotate', length_rotate' (l ++ [a]) n]; simp

lemma rotate'_eq_take_append_drop : ∀ {l : list α} {n : ℕ}, n ≤ l.length →
  l.rotate' n = l.drop n ++ l.take n
| []     n     h := by simp [drop_append_of_le_length h]
| l      0     h := by simp [take_append_of_le_length h]
| (a::l) (n+1) h :=
have hnl : n ≤ l.length, from le_of_succ_le_succ h,
have hnl' : n ≤ (l ++ [a]).length,
  by rw [length_append, length_cons, list.length, zero_add];
    exact (le_of_succ_le h),
by rw [rotate'_cons_succ, rotate'_eq_take_append_drop hnl', drop, take,
     drop_append_of_le_length hnl, take_append_of_le_length hnl];
   simp

lemma rotate'_rotate' : ∀ (l : list α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
| (a::l) 0     m := by simp
| []     n     m := by simp
| (a::l) (n+1) m := by rw [rotate'_cons_succ, rotate'_rotate', add_right_comm, rotate'_cons_succ]

@[simp] lemma rotate'_length (l : list α) : rotate' l l.length = l :=
by rw rotate'_eq_take_append_drop (le_refl _); simp

@[simp] lemma rotate'_length_mul (l : list α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
| 0     := by simp
| (n+1) :=
calc l.rotate' (l.length * (n + 1)) =
  (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length :
    by simp [-rotate'_length, nat.mul_succ, rotate'_rotate']
... = l : by rw [rotate'_length, rotate'_length_mul]

lemma rotate'_mod (l : list α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
calc l.rotate' (n % l.length) = (l.rotate' (n % l.length)).rotate'
    ((l.rotate' (n % l.length)).length * (n / l.length)) : by rw rotate'_length_mul
... = l.rotate' n : by rw [rotate'_rotate', length_rotate', nat.mod_add_div]

lemma rotate_eq_rotate' (l : list α) (n : ℕ) : l.rotate n = l.rotate' n :=
if h : l.length = 0 then by simp [length_eq_zero, *] at *
else by
  rw [← rotate'_mod, rotate'_eq_take_append_drop (le_of_lt (nat.mod_lt _ (nat.pos_of_ne_zero h)))];
  simp [rotate]

lemma rotate_cons_succ (l : list α) (a : α) (n : ℕ) :
  (a :: l : list α).rotate n.succ = (l ++ [a]).rotate n :=
by rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp] lemma mem_rotate : ∀ {l : list α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
| []     _ n     := by simp
| (a::l) _ 0     := by simp
| (a::l) _ (n+1) := by simp [rotate_cons_succ, mem_rotate, or.comm]

@[simp] lemma length_rotate (l : list α) (n : ℕ) : (l.rotate n).length = l.length :=
by rw [rotate_eq_rotate', length_rotate']

lemma rotate_eq_take_append_drop {l : list α} {n : ℕ} : n ≤ l.length →
  l.rotate n = l.drop n ++ l.take n :=
by rw rotate_eq_rotate'; exact rotate'_eq_take_append_drop

lemma rotate_rotate (l : list α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) :=
by rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp] lemma rotate_length (l : list α) : rotate l l.length = l :=
by rw [rotate_eq_rotate', rotate'_length]

@[simp] lemma rotate_length_mul (l : list α) (n : ℕ) : l.rotate (l.length * n) = l :=
by rw [rotate_eq_rotate', rotate'_length_mul]

lemma prod_rotate_eq_one_of_prod_eq_one [group α] : ∀ {l : list α} (hl : l.prod = 1) (n : ℕ),
  (l.rotate n).prod = 1
| []     _  _ := by simp
| (a::l) hl n :=
have n % list.length (a :: l) ≤ list.length (a :: l), from le_of_lt (nat.mod_lt _ dec_trivial),
by rw ← list.take_append_drop (n % list.length (a :: l)) (a :: l) at hl;
  rw [← rotate_mod, rotate_eq_take_append_drop this, list.prod_append, mul_eq_one_iff_inv_eq,
    ← one_mul (list.prod _)⁻¹, ← hl, list.prod_append, mul_assoc, mul_inv_self, mul_one]

end list
