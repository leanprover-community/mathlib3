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
    induction h generalizing h0,
    { exact this _ h0, },
    { refine lt_trans (h_ih h0) (this _ _), exact lt_trans h0 (lt_of_succ_le h_a) }}
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

end nat
