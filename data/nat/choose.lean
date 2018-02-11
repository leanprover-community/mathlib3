/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
Mostly based on Jeremy Avigad's choose file in lean 2
-/


import data.nat.basic

open nat
def choose : ℕ → ℕ → ℕ
| _              0  := 1
| 0        (succ k) := 0
| (succ n) (succ k) := choose n k + choose n (succ k)

@[simp]
lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := begin
  cases n with n,unfold choose,unfold choose,
end

@[simp]
lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt {n k : ℕ} : n < k → choose n k = 0 := begin
  revert k,
  induction n with n' hi,
  assume k nk,cases k,exact absurd nk dec_trivial,
  unfold choose,
  assume k nk,
  cases k with k',
  exact absurd nk dec_trivial,
  unfold choose,
  rw [@hi k' (lt_of_succ_lt_succ nk),@hi (k' + 1) (lt_of_succ_lt nk)],
end

@[simp]
lemma choose_self (n : ℕ) : choose n n = 1 := begin
  induction n with n' hi,simp!,simpa! [choose_eq_zero_of_lt (lt_succ_self _)],
end

@[simp]
lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 := choose_eq_zero_of_lt (lt_succ_self _)

@[simp]
lemma choose_one_right (n : ℕ) : choose n 1 = n := begin
  induction n with n' hi,unfold choose,unfold choose,simp[hi],
end

lemma choose_pos {n k : ℕ} : k ≤ n → 0 < choose n k := begin
  revert k,
  induction n with n' hi,assume k kn,
  rw eq_zero_of_le_zero kn,simp,exact dec_trivial,
  assume k kn,
  cases k with k',simp,exact dec_trivial,
  rw choose_succ_succ,
  exact add_pos_of_pos_of_nonneg (hi (le_of_succ_le_succ kn)) (zero_le _),
end

lemma succ_mul_choose_eq (n k : ℕ) : succ n * choose n k = choose (succ n) (succ k) * succ k := begin
  revert k,induction n with n' hi,assume k,
  simp,cases k with k',simp,simp,
  rw [choose_eq_zero_of_lt (dec_trivial : 1 < succ(succ k')),zero_mul],
  assume k,cases k with k',
  simp,
  rw [choose_succ_succ (succ n') (succ k'),add_mul,←hi,mul_succ,←hi,add_right_comm],
  rw [←mul_add,←choose_succ_succ,←succ_mul],
end

lemma choose_mul_fact_mul_fact {i j : ℕ} : j ≤ i → choose i j * fact j * fact (i - j) = fact i := begin
  revert j,
  induction i with i' hi,assume j ij,
  simp!,rw eq_zero_of_le_zero ij,simp!,
  assume j ij,
  cases j with j',simp!,
  unfold choose,rw [succ_sub_succ,add_mul,add_mul],
  have : choose i' j' * fact (succ j') * fact (i' - j') = choose i' j' * fact j' * fact (i' - j') * succ j' := by
  { unfold fact,simp[mul_comm,mul_assoc,mul_left_comm]},
  rw [this,hi (le_of_succ_le_succ ij)],
  cases lt_or_eq_of_le ij with ij' ij',
  have : i' - j' = succ (i' - succ j') := by {rw [←succ_sub (le_of_succ_le_succ ij'),succ_sub_succ]},
  rw [this,fact_succ (i' - succ j'),mul_comm (succ (i' - succ j')),← mul_assoc,hi (le_of_succ_le_succ ij'),←mul_add],
  rw [←succ_sub (le_of_succ_le_succ ij')],rw nat.add_sub_cancel' ij,unfold fact,rw mul_comm,
  rw [ij',choose_succ_self,zero_mul,zero_mul,add_zero,mul_comm],unfold fact,
end

theorem choose_def_alt {n k : ℕ} : k ≤ n → choose n k = fact n / (fact k * fact (n - k)) := begin
  assume kn,
  have := choose_mul_fact_mul_fact kn,rw [mul_assoc,eq_comm] at this,
  exact (nat.div_eq_of_eq_mul_left (mul_pos (fact_pos _) (fact_pos _)) this).symm,
end

theorem fact_mul_fact_dvd_fact {n k : ℕ} : k ≤ n → fact k * fact (n - k) ∣ fact n := begin
  assume kn,rw [←choose_mul_fact_mul_fact kn,mul_assoc],exact dvd_mul_left _ _,
end
