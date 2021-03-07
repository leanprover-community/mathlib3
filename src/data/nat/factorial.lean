/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn
-/
import data.nat.basic
/-!
# The factorial function

-/

namespace nat
variables {m n : ℕ}

/-- `nat.factorial n` is the factorial of `n`. -/
@[simp] def factorial : nat → nat
| 0        := 1
| (succ n) := succ n * factorial n

localized "notation n `!`:10000 := nat.factorial n" in nat

@[simp] theorem factorial_zero : 0! = 1! := rfl

@[simp] theorem factorial_succ (n : ℕ) : n.succ! = succ n * n! := rfl

@[simp] theorem factorial_one : 1! = 1 := rfl

theorem mul_factorial_pred (hn : 0 < n) : n * (n - 1)! = n! :=
nat.sub_add_cancel hn ▸ rfl

theorem factorial_pos : ∀ n, 0 < n!
| 0        := zero_lt_one
| (succ n) := mul_pos (succ_pos _) (factorial_pos n)

theorem factorial_ne_zero (n : ℕ) : n! ≠ 0 := ne_of_gt (factorial_pos _)

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m! ∣ n! :=
begin
  induction n with n IH; simp,
  { have := eq_zero_of_le_zero h, subst m, simp },
  { cases eq_or_lt_of_le h with he hl,
    { subst m, simp },
    { apply dvd_mul_of_dvd_right (IH (le_of_lt_succ hl)) } }
end

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n!
| (succ m) n _ h := dvd_of_mul_right_dvd (factorial_dvd_factorial h)

theorem factorial_le {m n} (h : m ≤ n) : m! ≤ n! :=
le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

lemma factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m! * m.succ ^ n ≤ (m + n)!
| m 0     := by simp
| m (n+1) :=
by  rw [← add_assoc, nat.factorial_succ, mul_comm (nat.succ _), pow_succ', ← mul_assoc];
  exact mul_le_mul factorial_mul_pow_le_factorial
    (nat.succ_le_succ (nat.le_add_right _ _)) (nat.zero_le _) (nat.zero_le _)

lemma monotone_factorial : monotone factorial := λ n m, factorial_le

lemma factorial_lt (h0 : 0 < n) : n! < m! ↔ n < m :=
begin
  split; intro h,
  { rw [← not_le], intro hmn, apply not_le_of_lt h (factorial_le hmn) },
  { have : ∀(n : ℕ), 0 < n → n! < n.succ!,
    { intros k hk, rw [factorial_succ, succ_mul, lt_add_iff_pos_left],
      apply mul_pos hk (factorial_pos k) },
    induction h with k hnk generalizing h0,
    { exact this _ h0, },
    { refine lt_trans (h_ih h0) (this _ _), exact lt_trans h0 (lt_of_succ_le hnk) }}
end

lemma one_lt_factorial : 1 < n! ↔ 1 < n :=
by { convert factorial_lt _, refl, exact one_pos }

lemma factorial_eq_one : n! = 1 ↔ n ≤ 1 :=
begin
  split; intro h,
  { rw [← not_lt, ← one_lt_factorial, h], apply lt_irrefl },
  { cases h with h h, refl, cases h, refl }
end

lemma factorial_inj (h0 : 1 < n!) : n! = m! ↔ n = m :=
begin
  split; intro h,
  { rcases lt_trichotomy n m with hnm|hnm|hnm,
    { exfalso, rw [← factorial_lt, h] at hnm, exact lt_irrefl _ hnm,
      rw [one_lt_factorial] at h0, exact lt_trans one_pos h0 },
    { exact hnm },
    { exfalso, rw [← factorial_lt, h] at hnm, exact lt_irrefl _ hnm,
      rw [h, one_lt_factorial] at h0, exact lt_trans one_pos h0 }},
  { rw h }
end

lemma self_le_factorial : ∀ n : ℕ, n ≤ n!
| 0 := zero_le_one
| (k+1) := le_mul_of_one_le_right k.zero_lt_succ.le (nat.one_le_of_lt $ nat.factorial_pos _)

lemma lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n! :=
begin
  rw [← succ_pred_eq_of_pos ((zero_lt_two.trans (lt.base 2)).trans_le hi), factorial_succ],
  exact lt_mul_of_one_lt_right ((pred n).succ_pos) ((one_lt_two.trans_le
    (le_pred_of_lt (succ_le_iff.mp hi))).trans_le (self_le_factorial _)),
end

lemma add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + (n + 1)! < (i + n + 1)! :=
begin
  rw [factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i ≤ i + n := le.intro rfl,
  exact add_lt_add_of_lt_of_le (this.trans_lt ((lt_mul_iff_one_lt_right (zero_lt_two.trans_le
    (hi.trans this))).mpr (lt_iff_le_and_ne.mpr ⟨(i + n).factorial_pos, λ g,
    nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩))) (factorial_le
    ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi)))),
end

lemma add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
  i + n! < (i + n)! :=
begin
  cases hn,
  { rw factorial_one,
    exact lt_factorial_self (succ_le_succ hi) },
  { exact add_factorial_succ_lt_factorial_add_succ _ hi }
end

lemma add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) :
  i + (n + 1)! ≤ (i + (n + 1))! :=
begin
  by_cases i2 : 2 ≤ i,
  { exact (n.add_factorial_succ_lt_factorial_add_succ i2).le },
  { cases (not_le.mp i2) with _ i0,
    { change 1 + (n + 1)! ≤ (1 + n + 1) * (1 + n)!,
      rw [add_mul, one_mul, add_comm 1 n],
      exact (add_le_add_iff_right _).mpr (one_le_mul (nat.le_add_left 1 n) (n + 1).factorial_pos) },
    { rw [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp i0), zero_add, zero_add] } }
end

lemma add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) :
  i + n! ≤ (i + n)! :=
begin
  cases n1 with h,
  { exact self_le_factorial _ },
  { exact add_factorial_succ_le_factorial_add_succ i h }
end

end nat
