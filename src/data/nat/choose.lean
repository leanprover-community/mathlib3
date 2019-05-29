/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
Mostly based on Jeremy Avigad's choose file in lean 2
-/
import data.nat.basic data.nat.prime
import algebra.big_operators algebra.commute

open nat

lemma nat.prime.dvd_choose {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k :=
have h₁ : p ∣ fact p, from hp.dvd_fact.2 (le_refl _),
have h₂ : ¬p ∣ fact k, from mt hp.dvd_fact.1 (not_le_of_gt hkp),
have h₃ : ¬p ∣ fact (p - k), from mt hp.dvd_fact.1 (not_le_of_gt (nat.sub_lt_self hp.pos hk)),
by rw [← choose_mul_fact_mul_fact (le_of_lt hkp), mul_assoc, hp.dvd_mul, hp.dvd_mul] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

section binomial
open finset

variables {α : Type*}

/-- The binomial theorem -/
theorem add_pow_comm [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (x + y) ^ n = (range (succ n)).sum (λ m, x ^ m * y ^ (n - m) * choose n m) :=
begin
  let t : ℕ → ℕ → α := λ n i, x ^ i * (y ^ (n - i)) * (choose n i),
  change (x + y) ^ n = (range n.succ).sum (t n),
  have h_first : ∀ n, t n 0 = y ^ n :=
    λ n, by { dsimp [t], rw[choose_zero_right, nat.cast_one, mul_one, one_mul] },
  have h_last : ∀ n, t n n.succ = 0 :=
    λ n, by { dsimp [t], rw [choose_succ_self, nat.cast_zero, mul_zero] },
  have h_middle : ∀ (n i : ℕ), (i ∈ finset.range n.succ) →
   ((t n.succ) ∘ nat.succ) i = x * (t n i) + y * (t n i.succ) :=
  begin
    intros n i h_mem,
    have h_le : i ≤ n := nat.le_of_lt_succ (finset.mem_range.mp h_mem),
    dsimp [t],
    rw [choose_succ_succ, nat.cast_add, mul_add],
    congr' 1,
    { rw[pow_succ x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc] },
    { rw[← mul_assoc y, ← mul_assoc y, (h.symm.pow i.succ).eq],
      by_cases h_eq : i = n,
      { rw [h_eq, choose_succ_self, nat.cast_zero, mul_zero, mul_zero] },
      { rw[succ_sub (lt_of_le_of_ne h_le h_eq)],
        rw[pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc] } }
  end,
  induction n with n ih,
  { rw [_root_.pow_zero, sum_range_succ, range_zero, sum_empty, add_zero],
    dsimp [t], rw [choose_self, nat.cast_one, mul_one, mul_one] },
  { rw[sum_range_succ', h_first],
    rw[finset.sum_congr rfl (h_middle n), finset.sum_add_distrib, add_assoc],
    rw[pow_succ (x + y), ih, add_mul, finset.mul_sum, finset.mul_sum],
    congr' 1,
    rw[finset.sum_range_succ', finset.sum_range_succ, h_first, h_last,
       mul_zero, zero_add, _root_.pow_succ] }
end

theorem add_pow [comm_semiring α] (x y : α) (n : ℕ) :
  (x + y) ^ n = (range (succ n)).sum (λ m, x ^ m * y ^ (n - m) * choose n m) :=
add_pow_comm (commute.all x y) n

end binomial
