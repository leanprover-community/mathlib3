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
(note that `1979` is prime). Hence the `1979`-adic valuation of each fraction is positive,
and thus the `1979`-adic valuation of the sum is also positive.

## Remarks on the formalisation

The p-adic valuation function on ℚ is ℤ-valued and hence has v(0)=0 (rather than +∞);
we thus had to occasionally deal with funny edge cases which aren't there mathematically.
In retrospect it might have been easier to work with p-adic norms, which are ℚ-valued
and don't have this problem.
-/

open finset nat
open_locale big_operators

instance : fact (nat.prime 1979) := by {rw fact_iff, norm_num}

namespace imo1979q1

/-
  The goal is equivalent to showing that the 1979-adic valuation of the sum
  ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n is positive.

  We start with some lemmas:

  Lemma 1 : ∑ n in Icc 1 1319, 1 / n - ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n =
    ∑ n in Icc 1 659, 1 / n
  Lemma 2 : ∑ n in Icc 1 659, 1 / n + ∑ n in Icc 660 1319, 1 / n = ∑ n in Icc 1 1319, 1 / n
  Corollary 3 : ∑ n in Icc 1 1319, (-1) ^ (n + 1) / n = ∑ n in Icc 660 1319, 1 / n
  Lemma 4 : ∑ n in Icc 660 1319, 1 / n = ∑ n in range 330, 1 / (n + 660) +
    ∑ n in range 330, 1 / (1319 - n)

  Then we prove the theorem, by showing the 1979-adic valuation of the sum
  ∑ n in range 330, 1 / (n + 660) + ∑ n in range 330, 1 / (1319 - n) is positive.
-/

/-- The injection ℕ ↪ ℕ sending any n ∈ ℕ to 2 * n
-/
abbreviation double : ℕ ↪ ℕ := ⟨λ n, 2 * n, mul_right_injective dec_trivial⟩

lemma lemma1 : ∑ n in Icc (1 : ℕ) 1319, (1 : ℚ) / n - ∑ n in Icc (1 : ℕ) 1319, (-1) ^ (n + 1) / n =
  ∑ n in Icc (1 : ℕ) 659, 1 / n :=
calc  ∑ n in Icc (1 : ℕ) 1319, (1 : ℚ) / n - ∑ n in Icc (1 : ℕ) 1319, (-1) ^ (n + 1) / n
    = ∑ n in Icc (1 : ℕ) 1319, (1 / n - (-1) ^ (n+1) / n) : by rw sum_sub_distrib
... = ∑ n in Icc (1 : ℕ) 1319, ite (even n) (2 / n) 0 : begin
      apply sum_congr rfl,
      rintro x -,
      rw [pow_succ, neg_one_mul, neg_div, sub_neg_eq_add, div_add_div_same],
      split_ifs,
      { rw [neg_one_pow_of_even h], norm_num },
      { rw [neg_one_pow_of_odd (odd_iff_not_even.2 h), add_neg_self, zero_div] }
    end
... = ∑ (x : ℕ) in filter even (Icc (1 : ℕ) 1319), 2 / x : by rw sum_filter
... = ∑ (x : ℕ) in map double (Icc (1 : ℕ) 659), 2 / x : begin
      apply sum_congr (finset.ext $ λ x, _) (λ _ _, rfl),
      simp only [mem_filter, mem_map, mem_Icc, exists_prop],
      split,
      { rintros ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩,
        exact ⟨a, ⟨by linarith, by linarith⟩, rfl⟩ },
      { rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩,
        refine ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, a, rfl⟩, }
    end
... = ∑ n in Icc (1 : ℕ) 659, 1 / n : begin
      rw sum_map (Icc (1 : ℕ) 659) double (λ n, (2 : ℚ) / n),
      apply sum_congr rfl,
      rintro x -,
      convert show 2/ ((2 : ℚ) * x) = 1 / x, from div_mul_right _ two_ne_zero,
      field_simp,
    end

lemma lemma2 : ∑ n in Icc (1 : ℕ) 659, (1 : ℚ) / n + ∑ n in Icc (660 : ℕ) 1319, 1 / n =
  ∑ n in Icc (1 : ℕ) 1319, 1 / n :=
by rw [← Ico_succ_right, ← Ico_succ_right, sum_Ico_consecutive, Ico_succ_right]; dec_trivial


lemma corollary3 : ∑ n in Icc (1 : ℕ) 1319, (-1 : ℚ) ^ (n + 1) / n =
  ∑ n in Icc (660 : ℕ) 1319, 1 / n :=
begin
  apply @add_left_cancel _ _ (∑ n in Icc (1 : ℕ) 659, (1 : ℚ) / n),
  rw [lemma2, ← lemma1, sub_add_cancel]
end

lemma lemma4 : ∑ n in range 330, (1 : ℚ) / (n + 660) + ∑ n in range 330, 1 / (1319 - n) =
  ∑ n in Icc (660 : ℕ) 1319, 1 / n :=
calc ∑ (n : ℕ) in range 330, 1 / (n + 660 : ℚ) + ∑ (n : ℕ) in range 330, 1 / (1319 - ↑n)
    = ∑ (m : ℕ) in Ico 660 990, 1 / m + ∑ (n : ℕ) in range 330, 1 / (1319 - ↑n) : begin
      rw sum_Ico_eq_sum_range,
      simp_rw [show ∀ (n : ℚ), n + 660 = 660 + n, from λ _, add_comm _ _],
      norm_num,
    end
... = ∑ (m : ℕ) in Ico 660 990, 1 / m + ∑ (n : ℕ) in range 330, 1 / ((1319 - n : ℕ) : ℚ) : begin
      refine congr_arg ((+) _) (sum_congr rfl (λ n hn, _)),
      rw mem_range at hn,
      rw [one_div, one_div, inv_inj₀, sub_eq_iff_eq_add],
      norm_cast,
      rw nat.sub_add_cancel,
      linarith,
    end
... = ∑ (m : ℕ) in Ico 660 990, 1 / m + ∑ (m : ℕ) in Icc 990 1319, 1 / m : begin
      rw [range_eq_Ico, ← Ico_succ_right],
      have := congr_arg ((+) (∑ (m : ℕ) in Ico 660 990, 1 /(m : ℚ)))
        (sum_Ico_reflect (λ x, 1 / x : ℕ → ℚ) 0 (show 330 ≤ 1319 + 1, by norm_num)),
      exact this,
    end
... = ∑ n in Icc (660 : ℕ) 1319, 1 / (n : ℚ) : begin
      rw [← Ico_succ_right, sum_Ico_consecutive, Ico_succ_right]; norm_num
    end
... = _ : by rw [←Ico_succ_right, sum_Ico_eq_sum_range]

lemma easy1 {n : ℕ} (hn : n < 330) : padic_val_rat 1979 (n + 660) = 0 :=
begin
  rw (show (n : ℚ) + 660 = (n + 660 : ℕ), by norm_num),
  rw ← padic_val_rat_of_nat,
  norm_cast,
  apply padic_val_nat_of_not_dvd,
  apply nat.not_dvd_of_pos_of_lt; linarith,
end

lemma easy2 {n : ℕ} (hn : n < 330) : padic_val_rat 1979 (1319 - n) = 0 :=
begin
  have h : (1319 : ℚ) - n = (1319 - n : ℕ),
  { rw nat.cast_sub,
    { norm_cast },
    { linarith }},
  rw [h, ← padic_val_rat_of_nat],
  norm_cast,
  apply padic_val_nat_of_not_dvd,
  apply nat.not_dvd_of_pos_of_lt,
  { apply nat.sub_pos_of_lt,
   linarith },
  { apply lt_of_le_of_lt _ (show 1319 < 1979, by linarith),
    exact nat.sub_le 1319 n }
end


lemma lemma5 : ∀ n ∈ range 330, padic_val_rat 1979 ((1 / (n + 660) + 1 / (1319 - n)) : ℚ) = 1 :=
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
  have h2' : 0 ≤ (1319 : ℤ) - n,
  { have h3 : (n : ℤ) < 330, {norm_cast, exact hn},
    linarith },
  have h3 : (1 : ℚ) / (n + 660) + 1 / (1319 - n) = 1979 / ((n + 660) * (1319 - n)),
  { field_simp [h1, h2],
    generalize : (n : ℚ) = q,
    ring },
  rw h3, clear h3,
  rw padic_val_rat.div 1979 (show (1979 : ℚ) ≠ 0, by norm_num) (mul_ne_zero h1 h2),
  have h := padic_val_rat.padic_val_rat_self (show 1 < 1979, by norm_num),
  rw (show ((1979 : ℕ) : ℚ) = 1979, by norm_cast) at h,
  rw h,
  suffices : 0 = padic_val_rat 1979 ((n + 660) * (1319 - n)), { linarith },
  rw padic_val_rat.mul 1979 h1 h2,
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
  suffices : 0 < padic_val_rat 1979 p,
  { rw ← padic_val_rat_of_nat at this,
    have h2 : 0 < padic_val_nat 1979 p,
      assumption_mod_cast,
    exact dvd_of_one_le_padic_val_nat h2 },
  have hp' : (p : ℚ) ≠ 0,
  { norm_cast,
    linarith },
  have hq' : (q : ℚ) ≠ 0,
  { norm_cast,
    linarith },
  suffices : 0 < padic_val_rat 1979 (p / q),
  { rw [padic_val_rat.div 1979 hp' hq', ← padic_val_rat_of_nat _ q] at this,
    apply lt_of_lt_of_le this,
    apply sub_le_self,
    norm_cast,
    exact zero_le' },
  rw h,
  apply padic_val_rat.sum_pos_of_pos,
  { intros i hi,
    rw lemma5 i (mem_range.2 hi),
    exact zero_lt_one },
  { rw ← h,
    exact div_ne_zero hp' hq' }
end

end imo1979q1
