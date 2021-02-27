/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import data.nat.choose.basic
import tactic.linarith
import algebra.big_operators.ring
import algebra.big_operators.intervals
import algebra.big_operators.order
/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/
open nat
open finset

open_locale big_operators

variables {R : Type*}

/-- A version of the binomial theorem for noncommutative semirings. -/
theorem commute.add_pow [semiring R] {x y : R} (h : commute x y) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
begin
  let t : ℕ → ℕ → R := λ n m, x ^ m * (y ^ (n - m)) * (choose n m),
  change (x + y) ^ n = ∑ m in range (n + 1), t n m,
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
    { rw[← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq],
      by_cases h_eq : i = n,
      { rw [h_eq, choose_succ_self, nat.cast_zero, mul_zero, mul_zero] },
      { rw[succ_sub (lt_of_le_of_ne h_le h_eq)],
        rw[pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc] } }
  end,
  induction n with n ih,
  { rw [pow_zero, sum_range_succ, range_zero, sum_empty, add_zero],
    dsimp [t], rw [choose_self, nat.cast_one, mul_one, mul_one] },
  { rw[sum_range_succ', h_first],
    rw[finset.sum_congr rfl (h_middle n), finset.sum_add_distrib, add_assoc],
    rw[pow_succ (x + y), ih, add_mul, finset.mul_sum, finset.mul_sum],
    congr' 1,
    rw[finset.sum_range_succ', finset.sum_range_succ, h_first, h_last,
       mul_zero, zero_add, pow_succ] }
end

/-- The binomial theorem -/
theorem add_pow [comm_semiring R] (x y : R) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
(commute.all x y).add_pow n

lemma pow_mul_pow_mul_choose_le [ordered_comm_semiring R] {n k : ℕ} (h : k ≤ n)
  {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  a ^ k * b ^ (n - k) * choose n k ≤ (a + b) ^ n :=
begin
  rw add_pow,
  refine single_le_sum (λ l hl, _) (mem_range.2 $ nat.lt_succ_of_le h),
  exact mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)) (nat.cast_nonneg _)
end

lemma choose_le_add_pow_div_pow_div_pow {𝕜 : Type*} [linear_ordered_field 𝕜] {n k : ℕ} (h : k ≤ n)
  {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) :
  ↑(choose n k) ≤ (a + b) ^ n / (a ^ k * b ^ (n - k)) :=
(le_div_iff' $ mul_pos (pow_pos ha k) (pow_pos hb (n - k))).2 $
  pow_mul_pow_mul_choose_le h ha.le hb.le

namespace nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) :
  ∑ m in range (n + 1), choose n m = 2 ^ n :=
by simpa using (add_pow 1 1 n).symm

lemma sum_range_choose_halfway (m : nat) :
  ∑ i in range (m + 1), choose (2 * m + 1) i = 4 ^ m :=
have ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) =
  ∑ i in range (m + 1), choose (2 * m + 1) i,
from sum_congr rfl $ λ i hi, choose_symm $ by linarith [mem_range.1 hi],
(nat.mul_right_inj zero_lt_two).1 $
calc 2 * (∑ i in range (m + 1), choose (2 * m + 1) i) =
  (∑ i in range (m + 1), choose (2 * m + 1) i) +
    ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) :
  by rw [two_mul, this]
... = (∑ i in range (m + 1), choose (2 * m + 1) i) +
  ∑ i in Ico (m + 1) (2 * m + 2), choose (2 * m + 1) i : begin
    rw [range_eq_Ico, sum_Ico_reflect],
    { congr,
      have A : m + 1 ≤ 2 * m + 1, by linarith,
      rw [add_comm, nat.add_sub_assoc A, ← add_comm],
      congr,
      rw nat.sub_eq_iff_eq_add A,
      ring, },
   { linarith }
  end
... = ∑ i in range (2 * m + 2), choose (2 * m + 1) i : sum_range_add_sum_Ico _ (by linarith)
... = 2^(2 * m + 1) : sum_range_choose (2 * m + 1)
... = 2 * 4^m : by { rw [pow_succ, pow_mul], refl }

lemma choose_middle_le_pow (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n :=
begin
  have t : choose (2 * n + 1) n ≤ ∑ i in range (n + 1), choose (2 * n + 1) i :=
    single_le_sum (λ x _, by linarith) (self_mem_range_succ n),
  simpa [sum_range_choose_halfway n] using t
end

end nat

theorem int.alternating_sum_range_choose {n : ℕ} :
  ∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ) = if n = 0 then 1 else 0 :=
begin
  cases n, { simp },
  have h := add_pow (-1 : ℤ) 1 n.succ,
  simp only [one_pow, mul_one, add_left_neg, int.nat_cast_eq_coe_nat] at h,
  rw [← h, zero_pow (nat.succ_pos n), if_neg (nat.succ_ne_zero n)],
end

theorem int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
  ∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ) = 0 :=
by rw [int.alternating_sum_range_choose, if_neg h0]

namespace finset

theorem sum_powerset_apply_card {α β : Type*} [add_comm_monoid α] (f : ℕ → α) {x : finset β} :
  ∑ m in x.powerset, f m.card = ∑ m in range (x.card + 1), (x.card.choose m) •ℕ f m :=
begin
  transitivity ∑ m in range (x.card + 1), ∑ j in x.powerset.filter (λ z, z.card = m), f j.card,
  { refine (sum_fiberwise_of_maps_to _ _).symm,
    intros y hy,
    rw [mem_range, nat.lt_succ_iff],
    rw mem_powerset at hy,
    exact card_le_of_subset hy },
  { refine sum_congr rfl (λ y hy, _),
    rw [← card_powerset_len, ← sum_const],
    refine sum_congr powerset_len_eq_filter.symm (λ z hz, _),
    rw (mem_powerset_len.1 hz).2 }
end

theorem sum_powerset_neg_one_pow_card {α : Type*} [decidable_eq α] {x : finset α} :
  ∑ m in x.powerset, (-1 : ℤ) ^ m.card = if x = ∅ then 1 else 0 :=
begin
  rw sum_powerset_apply_card,
  simp only [nsmul_eq_mul', ← card_eq_zero],
  convert int.alternating_sum_range_choose,
  ext,
  simp,
end

theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : finset α}
  (h0 : x.nonempty) :
  ∑ m in x.powerset, (-1 : ℤ) ^ m.card = 0 :=
begin
  classical,
  rw [sum_powerset_neg_one_pow_card, if_neg],
  rw [← ne.def, ← nonempty_iff_ne_empty],
  apply h0,
end

end finset
