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
lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n;refl

@[simp]
lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt {n : ℕ} : ∀ {k}, n < k → choose n k = 0 :=
begin
  induction n with n hi,
  { assume k hk, cases k,
    exact absurd hk dec_trivial,
    exact choose_zero_succ _ },
  { assume k hk,
    cases k with k',
      {exact absurd hk dec_trivial},
    unfold choose,
    rw [@hi _ (lt_of_succ_lt_succ hk),@hi _ (lt_of_succ_lt hk)] }
end

@[simp]
lemma choose_self (n : ℕ) : choose n n = 1 :=
begin
  induction n with n' hi, 
  { simp [choose] },
  { simpa! [choose_eq_zero_of_lt (lt_succ_self _)] }
end

@[simp]
lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 := choose_eq_zero_of_lt (lt_succ_self _)

@[simp]
lemma choose_one_right (n : ℕ) : choose n 1 = n :=
begin
  induction n with n' hi,
  { refl },
  { unfold choose,simp[hi] }
end

lemma choose_pos {n : ℕ} : ∀ {k}, k ≤ n → 0 < choose n k :=
begin
  induction n with n' hi,
  { simp [nat.le_zero_iff] {contextual := tt},
    exact dec_trivial },
  assume k hk,
  cases k with k',
  { simp, exact dec_trivial },
  { rw choose_succ_succ,
    exact add_pos_of_pos_of_nonneg (hi (le_of_succ_le_succ hk)) (zero_le _) }
end

lemma succ_mul_choose_eq (n : ℕ) : ∀ k, succ n * choose n k = choose (succ n) (succ k) * succ k := 
begin
  induction n with n' hi,
  { assume k,
    rw [one_mul, choose_succ_succ, choose_zero_succ, add_zero],
    cases k with k', 
      simp,
      rw [choose_zero_succ,zero_mul] },
  assume k,
  cases k with k',
  { simp},
  { rw [choose_succ_succ (succ n') (succ k'), add_mul, ←hi,mul_succ, ←hi,add_right_comm],
    rw [←mul_add, ←choose_succ_succ,←succ_mul] }
end

lemma choose_mul_fact_mul_fact {n : ℕ} : ∀ {k}, k ≤ n → choose n k * fact k * fact (n - k) = fact n :=
begin
  induction n with n' hi,
  { assume k hnk,
    rw eq_zero_of_le_zero hnk, simp },
  { assume k hnk,
    cases k with k', 
    { simp},
    { rw [choose_succ_succ, succ_sub_succ, add_mul, add_mul],
      have : choose n' k' * fact (succ k') * fact (n' - k') = choose n' k' * fact k' * fact (n' - k') * succ k' := by
      { unfold fact, simp[mul_comm, mul_assoc, mul_left_comm] },
      rw [this, hi (le_of_succ_le_succ hnk)],
      cases lt_or_eq_of_le hnk with hnk₁ hnk₁,
      { have : n' - k' = succ (n' - succ k') := by rw [←succ_sub (le_of_succ_le_succ hnk₁),succ_sub_succ],
        rw [this, fact_succ (n' - succ k'), mul_comm (succ (n' - succ k')),←mul_assoc,hi (le_of_succ_le_succ hnk₁),←mul_add],
        rw [←succ_sub (le_of_succ_le_succ hnk₁), nat.add_sub_cancel' hnk, mul_comm, fact_succ] },
      { rw [hnk₁, choose_succ_self, zero_mul, zero_mul, add_zero, fact_succ, mul_comm] } } }
end

theorem choose_def_alt {n k : ℕ} : k ≤ n → choose n k = fact n / (fact k * fact (n - k)) :=
begin
  assume hk,
  have := choose_mul_fact_mul_fact hk,
  rw [mul_assoc, eq_comm] at this,
  exact (nat.div_eq_of_eq_mul_left (mul_pos (fact_pos _) (fact_pos _)) this).symm
end

theorem fact_mul_fact_dvd_fact {n k : ℕ} : k ≤ n → fact k * fact (n - k) ∣ fact n :=
begin
  assume hk,rw [←choose_mul_fact_mul_fact hk, mul_assoc], exact dvd_mul_left _ _
end
