/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.big_operators.ring
import data.nat.interval
import data.nat.parity
import number_theory.padics.padic_norm
import tactic.linarith
import tactic.field_simp

/-!
# IMO 1979 Q1

Let `p` and `q` be positive integers such that

`p/q = 1 - 1/2 + 1/3 - 1/4 + ... - 1/1318 + 1/1319`

Prove that `p` is a multiple of `1979`.

## The solution

The proof we formalise is the following. Rewrite the sum as
`1 + 1/2 + 1/3 + ... + 1/1319 - 2 * (1/2 + 1/4 + 1/6 + ... + 1/1318) = 1/660 + 1/661 + ... + 1/1319`
and now re-arranging as `(1/660 + 1/1319) + (1/661 + 1/1318) + ...` we see that
the numerator of each fraction is `1979` and the denominator is coprime to `1979`
(note that `1979` is prime). Hence the `1979`-adic norm of each fraction is less than one,
and thus the `1979`-adic norm of the sum is also less than one, because of the
nonarchimedean property.

-/

open finset nat
open_locale big_operators

instance : fact (nat.prime 1979) := by {rw fact_iff, norm_num}

namespace imo1979q1

/-
  The goal is equivalent to showing that the 1979-adic norm of the sum
  ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n is less than one.

  We start with some lemmas:

  Lemma 1 : ∑ n in Icc 1 1319, 1 / n - ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n =
    ∑ n in Icc 1 659, 1 / n
  Lemma 2 : ∑ n in Icc 1 659, 1 / n + ∑ n in Icc 660 1319, 1 / n = ∑ n in Icc 1 1319, 1 / n
  Corollary 3 : ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n = ∑ n in Icc 660 1319, 1 / n
  Lemma 4 : ∑ n in Icc 660 1319, 1 / n = ∑ n in range 330, 1 / (n + 660) +
    ∑ n in range 330, 1 / (1319 - n)

  Then we prove the theorem, by showing the 1979-adic norm of the sum
  ∑ n in range 330, 1 / (n + 660) + ∑ n in range 330, 1 / (1319 - n) is less than one.
-/

/-- The injection ℕ ↪ ℕ sending any n ∈ ℕ to 2 * n
-/
def double : ℕ ↪ ℕ := ⟨λ n, 2 * n, mul_right_injective dec_trivial⟩

lemma double_apply (x : ℕ) : double x = x + x := two_mul x

lemma lemma1 : ∑ n in Icc (1 : ℕ) 1319, (1 : ℚ) / n - ∑ n in Icc (1 : ℕ) 1319, (-1) ^ (n + 1) / n =
  ∑ n in Icc (1 : ℕ) 659, 1 / n :=
begin
  let a : ℚ := ∑ n in Icc (1 : ℕ) 1319, (-1) ^ (n + 1) / n,
  let b : ℚ := ∑ n in Icc (1 : ℕ) 1319, 1 / n,
  calc b - a = ∑ n in Icc (1 : ℕ) 1319, (1 / n - (-1) ^ (n+1) / n) : by rw sum_sub_distrib
  ...        = ∑ n in Icc (1 : ℕ) 1319, ite (even n) (2 / n) 0 : by
  { apply sum_congr rfl,
    rintro x -,
    rw [pow_succ, neg_one_mul, neg_div, sub_neg_eq_add, div_add_div_same],
    split_ifs,
    { rw [h.neg_one_pow], norm_num },
    { rw [(odd_iff_not_even.2 h).neg_one_pow],
        simp only [zero_div, add_right_neg] } }
  ...        = ∑ (x : ℕ) in filter even (Icc (1 : ℕ) 1319), 2 / x : by rw sum_filter
  ...        = ∑ (x : ℕ) in map double (Icc (1 : ℕ) 659), 2 / x : by
  { apply sum_congr _ (λ _ _, rfl),
    ext x,
    rw [mem_filter, mem_map],
    split,
    { rintro ⟨ha, a, rfl⟩,
      simp_rw double_apply,
      refine ⟨a, _, rfl⟩,
      rw mem_Icc at ha ⊢,
      split;
      linarith },
    { rintro ⟨a, ha, rfl⟩,
      simp_rw double_apply,
      refine ⟨_, a, rfl⟩,
      rw mem_Icc at ha ⊢,
      split;
      linarith } }
    ...        = ∑ n in Icc (1 : ℕ) 659, 1 / n : by
    { rw sum_map (Icc (1 : ℕ) 659) double (λ n, (2 : ℚ) / n),
      apply sum_congr rfl,
      rintro x -,
      unfold double,
      norm_num,
      rw div_mul_right,
      exact two_ne_zero }
end

lemma lemma2 : ∑ n in Icc (1 : ℕ) 659, (1 : ℚ) / n + ∑ n in Icc (660 : ℕ) 1319, 1 / n =
  ∑ n in Icc (1 : ℕ) 1319, 1 / n :=
begin
  simp only [← Ico_succ_right],
  rw sum_Ico_consecutive;
  norm_num
end

lemma corollary3 : ∑ n in Icc (1 : ℕ) 1319, (-1 : ℚ) ^ (n + 1) / n =
  ∑ n in Icc (660 : ℕ) 1319, 1 / n :=
begin
  apply @add_left_cancel _ _ (∑ n in Icc (1 : ℕ) 659, (1 : ℚ) / n),
  rw [lemma2, ← lemma1, sub_add_cancel]
end

lemma lemma4 : ∑ n in range 330, (1 : ℚ) / (n + 660) + ∑ n in range 330, 1 / (1319 - n) =
  ∑ n in Icc (660 : ℕ) 1319, 1 / n :=
begin
  rw [← Ico_succ_right, sum_Ico_eq_sum_range],
  have h : ∑ (n : ℕ) in range 330, (1 : ℚ) / (n + 660) =
    ∑ (m : ℕ) in Ico 660 990, (1 : ℚ) / m,
  { rw sum_Ico_eq_sum_range,
    apply sum_congr rfl,
    intros i hi,
    norm_num,
    rw add_comm },
  rw h, clear h,
  have h : ∑ (n : ℕ) in range 330, (1 : ℚ) / (1319 - n) =
    ∑ (m : ℕ) in Icc 990 1319, (1 : ℚ) / m,
  { rw range_eq_Ico,
    have h : ∑ (m : ℕ) in Icc 990 1319, (1 : ℚ) / m =
      ∑ (m : ℕ) in Icc 990 1319, (λ (n : ℕ), (1 : ℚ) / (1319 - n)) (1319 - m),
    { apply sum_congr rfl,
      intros i hi,
      rw mem_Icc at hi,
      push_cast [hi.2],
      norm_num },
    rw h, clear h,
    rw ← Ico_succ_right,
    rw sum_Ico_reflect,
    norm_num },
  rw h, clear h,
  rw ← Ico_succ_right,
  rw sum_Ico_consecutive,
  { rw sum_Ico_eq_sum_range },
  { linarith },
  { norm_num }
end

-- waiting on #16704
/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
lemma nat_eq_one_iff {p : ℕ} [fact (nat.prime p)] (m : ℕ) : padic_norm p m = 1 ↔ ¬ p ∣ m :=
begin
  sorry
end


-- waiting on #16704
lemma nat_lt_one_iff {p : ℕ} [fact (nat.prime p)] (m : ℕ) : padic_norm p m < 1 ↔ p ∣ m :=
begin
  sorry
end

-- waiting on #16704
lemma padic_norm.of_nat {p : ℕ} [fact (nat.prime p)] (m : ℕ) : padic_norm p m ≤ 1 :=
padic_norm.of_int p (m : ℤ)

lemma easy1 {n : ℕ} (hn : n < 330) : padic_norm 1979 (n + 660) = 1 :=
begin
  norm_cast,
  haveI : fact (nat.prime 1979) := fact.mk (by norm_num),
  rw nat_eq_one_iff,
  apply nat.not_dvd_of_pos_of_lt; linarith,
end

-- waiting on #16704
lemma padic_norm.sum_lt {p : ℕ} {t : ℚ} [fact (nat.prime p)] {n : ℕ} {F : ℕ → ℚ}
  (hF : ∀ i, i < n → padic_norm p (F i) < t) (hn : 0 < n) :
  padic_norm p (∑ i in finset.range n, F i) < t :=
sorry

-- waiting on #16704
lemma padic_norm.sum_lt' {p : ℕ} {t : ℚ} [fact (nat.prime p)] {n : ℕ} {F : ℕ → ℚ}
  (hF : ∀ i, i < n → padic_norm p (F i) < t) (ht : 0 ≤ t) :
  padic_norm p (∑ i in finset.range n, F i) < t :=
sorry

lemma easy2 {n : ℕ} (hn : n < 330) : padic_norm 1979 (1319 - n) = 1 :=
begin
  have h : (1319 : ℚ) - n = (1319 - n : ℕ),
  { rw nat.cast_sub,
    { norm_cast },
    { linarith }},
  rw [h],
  rw nat_eq_one_iff,
  apply nat.not_dvd_of_pos_of_lt,
  { apply nat.sub_pos_of_lt,
   linarith },
  { apply lt_of_le_of_lt _ (show 1319 < 1979, by linarith),
    exact nat.sub_le 1319 n }
end


lemma lemma5 : ∀ n ∈ range 330, padic_norm 1979 ((1 / (n + 660) + 1 / (1319 - n)) : ℚ) < 1 :=
begin
  intros n hn,
  rw mem_range at hn,
  have h1 : (n : ℚ) + 660 ≠ 0,
  { apply ne_of_gt,
    norm_cast,
    apply succ_pos },
  have h2 : (1319 : ℚ) - n ≠ 0,
  { have h3 : (n : ℚ) < 330, {norm_cast, exact hn},
    linarith },
  have h3 : (1 : ℚ) / (n + 660) + 1 / (1319 - n) = 1979 / ((n + 660) * (1319 - n)),
  { field_simp [h1, h2],
    generalize : (n : ℚ) = q,
    ring },
  rw h3, clear h3,
  rw padic_norm.div,
  have h := padic_norm.padic_norm_p (show 1 < 1979, by norm_num),
  rw (show ((1979 : ℕ) : ℚ) = 1979, by norm_cast) at h,
  rw h,
  suffices : 1 = padic_norm 1979 ((n + 660) * (1319 - n)), { rw ← this, norm_num, },
  rw padic_norm.mul 1979,
  rw [easy1 hn, easy2 hn],
  exact self_eq_add_left.mpr rfl,
end

theorem imo1979_q1 (p q : ℕ) (hq : 0 < q) : (p : ℚ) / q =
  -- 1 - (1/2) + (1/3) - (1/4) + ... + (1/1319),
  ∑ n in Icc (1 : ℕ) 1319, (-1)^(n + 1) / n
  → 1979 ∣ p :=
begin
  rw corollary3,
  rw ← lemma4,
  intro h,
  rw ← sum_add_distrib at h,
  rcases nat.eq_zero_or_pos p with (rfl | hp),
  { exact dvd_zero 1979 },
  rw ← nat_lt_one_iff,
  have hq' : (q : ℚ) ≠ 0,
  { norm_cast,
    linarith },
  suffices : padic_norm 1979 (p / q) < 1,
  { rw [padic_norm.div 1979] at this,
    apply lt_of_le_of_lt _ this,
    apply le_div_self (padic_norm.nonneg 1979 ↑p),
    { exact (is_absolute_value.abv_pos (padic_norm 1979)).mpr hq', },
    apply padic_norm.of_nat, },
  rw h,
  refine padic_norm.sum_lt' _ (zero_le_one),
  intros i hi,
  apply lemma5,
  rwa mem_range,
end

end imo1979q1
