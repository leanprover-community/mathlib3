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

/-- `nat.fact n` is the factorial of `n`. -/
@[simp] def fact : nat → nat
| 0        := 1
| (succ n) := succ n * fact n

@[simp] theorem fact_zero : fact 0 = 1 := rfl

@[simp] theorem fact_succ (n) : fact (succ n) = succ n * fact n := rfl

@[simp] theorem fact_one : fact 1 = 1 := rfl

theorem fact_pos : ∀ n, 0 < fact n
| 0        := zero_lt_one
| (succ n) := mul_pos (succ_pos _) (fact_pos n)

theorem fact_ne_zero (n : ℕ) : fact n ≠ 0 := ne_of_gt (fact_pos _)

theorem fact_dvd_fact {m n} (h : m ≤ n) : fact m ∣ fact n :=
begin
  induction n with n IH; simp,
  { have := eq_zero_of_le_zero h, subst m, simp },
  { cases eq_or_lt_of_le h with he hl,
    { subst m, simp },
    { apply dvd_mul_of_dvd_right (IH (le_of_lt_succ hl)) } }
end

theorem dvd_fact : ∀ {m n}, 0 < m → m ≤ n → m ∣ fact n
| (succ m) n _ h := dvd_of_mul_right_dvd (fact_dvd_fact h)

theorem fact_le {m n} (h : m ≤ n) : fact m ≤ fact n :=
le_of_dvd (fact_pos _) (fact_dvd_fact h)

lemma fact_mul_pow_le_fact : ∀ {m n : ℕ}, m.fact * m.succ ^ n ≤ (m + n).fact
| m 0     := by simp
| m (n+1) :=
by  rw [← add_assoc, nat.fact_succ, mul_comm (nat.succ _), pow_succ', ← mul_assoc];
  exact mul_le_mul fact_mul_pow_le_fact
    (nat.succ_le_succ (nat.le_add_right _ _)) (nat.zero_le _) (nat.zero_le _)

lemma monotone_fact : monotone fact := λ n m, fact_le

lemma fact_lt (h0 : 0 < n) : n.fact < m.fact ↔ n < m :=
begin
  split; intro h,
  { rw [← not_le], intro hmn, apply not_le_of_lt h (fact_le hmn) },
  { have : ∀(n : ℕ), 0 < n → n.fact < n.succ.fact,
    { intros k hk, rw [fact_succ, succ_mul, lt_add_iff_pos_left],
      apply mul_pos hk (fact_pos k) },
    induction h generalizing h0,
    { exact this _ h0, },
    { refine lt_trans (h_ih h0) (this _ _), exact lt_trans h0 (lt_of_succ_le h_a) }}
end

lemma one_lt_fact : 1 < n.fact ↔ 1 < n :=
by { convert fact_lt _, refl, exact one_pos }

lemma fact_eq_one : n.fact = 1 ↔ n ≤ 1 :=
begin
  split; intro h,
  { rw [← not_lt, ← one_lt_fact, h], apply lt_irrefl },
  { cases h with h h, refl, cases h, refl }
end

lemma fact_inj (h0 : 1 < n.fact) : n.fact = m.fact ↔ n = m :=
begin
  split; intro h,
  { rcases lt_trichotomy n m with hnm|hnm|hnm,
    { exfalso, rw [← fact_lt, h] at hnm, exact lt_irrefl _ hnm,
      rw [one_lt_fact] at h0, exact lt_trans one_pos h0 },
    { exact hnm },
    { exfalso, rw [← fact_lt, h] at hnm, exact lt_irrefl _ hnm,
      rw [h, one_lt_fact] at h0, exact lt_trans one_pos h0 }},
  { rw h }
end

end nat
