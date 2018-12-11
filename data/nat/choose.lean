/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
Mostly based on Jeremy Avigad's choose file in lean 2
-/
import data.nat.basic data.nat.prime
import algebra.big_operators

open nat

def choose : ℕ → ℕ → ℕ
| _             0 := 1
| 0       (k + 1) := 0
| (n + 1) (k + 1) := choose n k + choose n (succ k)

@[simp] lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n; refl

@[simp] lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
| _             0 hk := absurd hk dec_trivial
| 0       (k + 1) hk := choose_zero_succ _
| (n + 1) (k + 1) hk :=
  have hnk : n < k, from lt_of_succ_lt_succ hk,
  have hnk1 : n < k + 1, from lt_of_succ_lt hk,
  by rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]

@[simp] lemma choose_self (n : ℕ) : choose n n = 1 :=
by induction n; simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]

@[simp] lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
choose_eq_zero_of_lt (lt_succ_self _)

@[simp] lemma choose_one_right (n : ℕ) : choose n 1 = n :=
by induction n; simp [*, choose]

lemma choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
| 0             _ hk := by rw [eq_zero_of_le_zero hk]; exact dec_trivial
| (n + 1)       0 hk := by simp; exact dec_trivial
| (n + 1) (k + 1) hk := by rw choose_succ_succ;
    exact add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (nat.zero_le _)


lemma succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
| 0             0 := dec_trivial
| 0       (k + 1) := by simp [choose]
| (n + 1)       0 := by simp
| (n + 1) (k + 1) :=
  by rw [choose_succ_succ (succ n) (succ k), add_mul, ←succ_mul_choose_eq, mul_succ,
  ←succ_mul_choose_eq, add_right_comm, ←mul_add, ←choose_succ_succ, ←succ_mul]

lemma choose_mul_fact_mul_fact : ∀ {n k}, k ≤ n → choose n k * fact k * fact (n - k) = fact n
| 0              _ hk := by simp [eq_zero_of_le_zero hk]
| (n + 1)        0 hk := by simp
| (n + 1) (succ k) hk :=
begin
  cases lt_or_eq_of_le hk with hk₁ hk₁,
  { have h : choose n k * fact (succ k) * fact (n - k) = succ k * fact n :=
      by rw ← choose_mul_fact_mul_fact (le_of_succ_le_succ hk);
      simp [fact_succ, mul_comm, mul_left_comm],
    have h₁ : fact (n - k) = (n - k) * fact (n - succ k) :=
      by rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), fact_succ],
    have h₂ : choose n (succ k) * fact (succ k) * ((n - k) * fact (n - succ k)) = (n - k) * fact n :=
      by rw ← choose_mul_fact_mul_fact (le_of_lt_succ hk₁);
      simp [fact_succ, mul_comm, mul_left_comm, mul_assoc],
    have h₃ : k * fact n ≤ n * fact n := mul_le_mul_right _ (le_of_succ_le_succ hk),
  rw [choose_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, h₂, ← add_one, add_mul, nat.mul_sub_right_distrib,
      fact_succ, ← nat.add_sub_assoc h₃, add_assoc, ← add_mul, nat.add_sub_cancel_left, add_comm] },
  { simp [hk₁, mul_comm, choose, nat.sub_self] }
end

theorem choose_eq_fact_div_fact {n k : ℕ} (hk : k ≤ n) : choose n k = fact n / (fact k * fact (n - k)) :=
begin
  have : fact n = choose n k * (fact k * fact (n - k)) :=
    by rw ← mul_assoc; exact (choose_mul_fact_mul_fact hk).symm,
  exact (nat.div_eq_of_eq_mul_left (mul_pos (fact_pos _) (fact_pos _)) this).symm
end

theorem fact_mul_fact_dvd_fact {n k : ℕ} (hk : k ≤ n) : fact k * fact (n - k) ∣ fact n :=
by rw [←choose_mul_fact_mul_fact hk, mul_assoc]; exact dvd_mul_left _ _

lemma nat.prime.dvd_choose {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k :=
have h₁ : p ∣ fact p, from hp.dvd_fact.2 (le_refl _),
have h₂ : ¬p ∣ fact k, from mt hp.dvd_fact.1 (not_le_of_gt hkp),
have h₃ : ¬p ∣ fact (p - k), from mt hp.dvd_fact.1 (not_le_of_gt (nat.sub_lt_self hp.pos hk)),
by rw [← choose_mul_fact_mul_fact (le_of_lt hkp), mul_assoc, hp.dvd_mul, hp.dvd_mul] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

section binomial
open finset

variables {α : Type*} [comm_semiring α] (x y : α)

/-- The binomial theorem -/
theorem add_pow :
  ∀ n : ℕ, (x + y) ^ n = (range (succ n)).sum (λ m, x ^ m * y ^ (n - m) * choose n m)
| 0        := by simp [range_succ]
| (succ n) :=
have h₁ : x * (x ^ n * y ^ (n - n) * choose n n) =
    x ^ succ n * y ^ (succ n - succ n) * choose (succ n) (succ n),
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have  h₂ : y * (x^0 * y^(n - 0) * choose n 0) = x^0 * y^(succ n - 0) * choose (succ n) 0,
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have h₃ : (range n).sum (λ m, x * (x ^ m * y ^ (n - m) * choose n m) + y *
    (x ^ succ m * y ^ (n - succ m) * choose n (succ m))) =
    (range n).sum (λ m, x ^ succ m * y ^ (succ n - succ m) * ↑(choose (succ n) (succ m))),
  from finset.sum_congr rfl $ λ m hm,
    begin
      simp only [mul_assoc, mul_left_comm y, mul_left_comm (y ^ (n - succ m)), mul_comm y],
      rw [← _root_.pow_succ', add_one, ← succ_sub (mem_range.1 hm)],
      simp [choose_succ_succ, mul_comm, mul_assoc, mul_left_comm, add_mul, mul_add, _root_.pow_succ]
    end,
by rw [_root_.pow_succ, add_pow, add_mul, finset.mul_sum, finset.mul_sum, sum_range_succ, sum_range_succ',
    sum_range_succ, sum_range_succ', add_assoc, ← add_assoc ((range n).sum _),
    ← finset.sum_add_distrib, h₁, h₂, h₃]

end binomial
