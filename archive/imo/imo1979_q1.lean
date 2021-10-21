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

instance : fact (nat.prime 1979) := by norm_num

namespace imo1979q1

def a : ℚ := ∑ n in range 1320, (-1)^(n + 1) / n
def b : ℚ := ∑ n in range 1320, 1 / n
def c : ℚ := ∑ n in range 660, 1 / n
def d : ℚ := ∑ n in Ico (660 : ℕ) 1320, 1 / n
def e : ℚ := ∑ n in range 330, 1 / (n + 660)
def f : ℚ := ∑ n in range 330, 1 / (1319 - n)

attribute [reducible] a b c d e f

/-
  The goal is equivalent to showing that the 1979-adic valuation of a is positive.

  We start with some lemmas:

  Lemma 1 : b - a = c
  Lemma 2 : c + d = b
  Corollary 3 : a = d
  Lemma 4 : d = e + f

  Then we prove the theorem, by showing the 1979-adic
  valuation of e + f is positive.
-/

def double : ℕ ↪ ℕ := ⟨λ n, 2 * n, mul_right_injective dec_trivial⟩

lemma lemma1 : b - a = c :=
  calc b - a = ∑ n in range 1320, (1/n - (-1)^(n+1)/n) : by rw sum_sub_distrib
    ... = ∑ n in range 1320, ite (even n) (2/n) 0 : by {
      apply sum_congr rfl,
      rintro x -,
      rw [pow_succ, neg_one_mul, neg_div, sub_neg_eq_add, div_add_div_same],
      split_ifs,
      { rw [neg_one_pow_of_even h], norm_num },
      { rw [neg_one_pow_of_odd (odd_iff_not_even.2 h)], simp } }
    ... = ∑ (x : ℕ) in filter even (range 1320), 2 / x : by rw sum_filter
    ... = ∑ (x : ℕ) in map double (range 660), 2 / x : by {
      apply sum_congr _ (λ _ _, rfl),
      ext x,
      rw [mem_filter, mem_map],
      split,
      { rintro ⟨ha, a, rfl⟩,
        refine ⟨a, _, rfl⟩,
        rw mem_range at ha ⊢,
        linarith },
      { rintro ⟨a, ha, rfl⟩,
        refine ⟨_, a, rfl⟩,
        rw mem_range at ha ⊢,
        change 2 * a < 1320,
        linarith } }
    ... = c : by {
      rw sum_map (range 660) double (λ n, (2 : ℚ) / n),
      apply sum_congr rfl,
      rintro x -,
      suffices : (2 : ℚ) / (2 * x) = 1 / x,
      { assumption_mod_cast },
      by_cases hq : (x : ℚ) = 0,
      { rw hq, simp },
      { field_simp [hq] } }

lemma lemma2 : c + d = b :=
begin
  unfold c d b,
  rw finset.Iio_eq_Ico,
  rw ← sum_union (Ico_disjoint_Ico_consecutive _ _ _),
  refine sum_congr (finset.Ico_union_Ico_eq_Ico _ _) (by {intros, refl});
    linarith,
end

lemma corollary3 : a = d :=
begin
  apply @add_left_cancel _ _ c,
  rw [lemma2, ← lemma1, sub_add_cancel],
end

--  have h : ∑ (n : ℕ) in Ico 0 330, (1 : ℚ) / (1319 - n) =
--    ∑ (m : ℕ) in Ico 990 1320, (1 : ℚ) / m,

-- move to finset
lemma finset.sum_add_right {α : Type*} [add_comm_monoid α] {f : ℕ → α} {a b c : ℕ} :
  ∑ (n : ℕ) in Ico a b, f (n + c) = ∑ m in Ico (a + c) (b + c), f m :=
begin
  rw [← Ico.image_add, sum_image],
  { simp_rw [add_comm] },
  rintro _ _ _ _,
  apply nat.add_right_injective c,
end

lemma finset.sum_add_left {α : Type*} [add_comm_monoid α] {f : ℕ → α} {a b c : ℕ} :
  ∑ (n : ℕ) in Ico a b, f (c + n) = ∑ m in Ico (c + a) (c + b), f m :=
begin
  rw [← Ico.add_image, sum_image],
  { simp_rw [add_comm] },
  rintro _ _ _ _,
  apply nat.add_right_injective c,
end

lemma lemma4 : e + f = d :=
begin
  unfold d e f,
  rw (Ico.zero_bot 330).symm,
  have h : ∑ (n : ℕ) in Ico 0 330, (1 : ℚ) / (n + 660) =
    ∑ (m : ℕ) in Ico 660 990, (1 : ℚ) / m,
  { rw [←Ico.image_add 0 330 660, sum_image],
    { apply sum_congr, refl,
      intros, simp [add_comm] },
    { intros x hx y hy,
      exact (add_right_inj 660).mp } },
  rw h, clear h,
  have h : ∑ (n : ℕ) in Ico 0 330, (1 : ℚ) / (1319 - n) =
    ∑ (m : ℕ) in Ico 990 1320, (1 : ℚ) / m,
  { have h2 : image (λ (j : ℕ), 1319 - j) (Ico 0 330) =
      Ico (990) (1320),
    { rw Ico.image_const_sub, refl, linarith },
    rw [← h2, sum_image],
    { apply sum_congr, refl,
      intros,
      apply congr_arg,
      rw nat.cast_sub, norm_cast,
      rw mem_Ico at H,
      cases H, linarith },
    { intros x hx y hy,
      intro h,
      rw [Ico.zero_bot, mem_range] at hx hy,
      rw nat.sub_eq_iff_eq_add (show x ≤ 1319, by linarith) at h,
      rw nat.sub_add_eq_add_sub (show y ≤ 1319, by linarith) at h,
      symmetry' at h,
      rw nat.sub_eq_iff_eq_add at h, swap, linarith,
      exact (add_right_inj 1319).mp h } },
  rw h, clear h,
  rw ←sum_union,
  { apply sum_congr,
    { apply Ico_union_Ico_eq_Ico; linarith },
    { intros, refl } },
  { apply Ico_disjoint_Ico_consecutive }
end

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
    rw nat.cast_sub,
    { norm_cast },
    { linarith },
  rw [h, ← padic_val_rat_of_nat],
  norm_cast,
  apply padic_val_nat_of_not_dvd,
  apply nat.not_dvd_of_pos_of_lt,
    apply nat.sub_pos_of_lt, linarith,
  rw nat.sub_lt_right_iff_lt_add; linarith,
end


lemma lemma5 : ∀ n ∈ range 330, padic_val_rat 1979 ((1 / (n + 660) + 1 / (1319 - n)) : ℚ) = 1 :=
begin
  intros n hn,
  rw mem_range at hn,
  have h1 : (n : ℚ) + 660 ≠ 0,
    apply ne_of_gt,
    norm_cast, simp,
  have h2 : (1319 : ℚ) - n ≠ 0,
    have h3 : (n : ℚ) < 330, norm_cast, exact hn,
    linarith,
  have h2' : 0 ≤ (1319 : ℤ) - n,
    have h3 : (n : ℤ) < 330, norm_cast, exact hn,
    linarith,
  have h3 : (1 : ℚ) / (n + 660) + 1 / (1319 - n) = 1979 / ((n + 660) * (1319 - n)),
    field_simp [h1, h2],
    generalize : (n : ℚ) = q,
    ring,
  rw h3, clear h3,
  rw padic_val_rat.div 1979 (show (1979 : ℚ) ≠ 0, by norm_num) (mul_ne_zero h1 h2),
  have h := padic_val_rat.padic_val_rat_self (show 1 < 1979, by norm_num),
  rw (show ((1979 : ℕ) : ℚ) = 1979, by norm_cast) at h,
  rw h,
  suffices : 0 = padic_val_rat 1979 ((↑n + 660) * (1319 - ↑n)),
    linarith,
  rw padic_val_rat.mul 1979 h1 h2,
  rw [easy1 hn, easy2 hn],
  simp,
end

theorem imo1979_q1 (p q : ℕ) (hq : 0 < q) : (p : ℚ) / q =
  -- 1 - (1/2) + (1/3) - (1/4) + ... + (1/1319),
  ∑ n in finset.range 1320, (-1)^(n + 1) / n
  → 1979 ∣ p :=
begin
  change _ = a → _,
  rw corollary3,
  rw ← lemma4,
  intro h,
  unfold e f at h,
  rw ← sum_add_distrib at h,
  rcases nat.eq_zero_or_pos p with (rfl | hp),
    simp,
  suffices : 0 < padic_val_rat 1979 p,
  { rw ← padic_val_rat_of_nat at this,
    have h2 : 0 < padic_val_nat 1979 p,
      assumption_mod_cast,
    exact dvd_of_one_le_padic_val_nat h2 },
  have hp' : (p : ℚ) ≠ 0,
  { intro hp2,
    have hp3 : p = 0,
    assumption_mod_cast,
    subst hp3,
    exact lt_irrefl 0 hp },
  have hq' : (q : ℚ) ≠ 0,
  { intro hq2,
    have hq3 : q = 0,
    assumption_mod_cast,
    subst hq3,
    exact lt_irrefl 0 hq },
  suffices : 0 < padic_val_rat 1979 (p / q),
  { rw [padic_val_rat.div 1979 hp' hq', ← padic_val_rat_of_nat _ q] at this,
    apply lt_of_lt_of_le this,
    apply sub_le_self,
    norm_cast, simp },
  rw h,
  apply padic_val_rat.sum_pos_of_pos,
  { intros i hi,
    rw lemma5 i (mem_range.2 hi),
    exact zero_lt_one },
  { rw ← h,
    exact div_ne_zero hp' hq' }
end

end imo1979q1
