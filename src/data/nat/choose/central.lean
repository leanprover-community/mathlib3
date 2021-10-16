/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/

import data.nat.choose.basic
import data.nat.choose.sum

open_locale nat
namespace nat

/-
Facts about the central binomial coefficient, two_mul_n_choose_n.
-/

lemma central_binom_ne_zero (n : ℕ) : (2 * n).choose n ≠ 0 :=
(choose_pos (nat.le_mul_of_pos_left zero_lt_two)).ne'

lemma choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ choose (2 * n) n :=
begin
  calc (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) : choose_le_middle r (2 * n)
  ... = (2 * n).choose n : by rw nat.mul_div_cancel_left n zero_lt_two
end

lemma two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ (2 * n).choose n :=
begin
  calc 2 ≤ (2 * n).choose 1 :
    begin
      simp only [choose_one_right],
      exact le_mul_of_pos_right n_pos,
    end
   ... ≤ (2 * n).choose n : choose_le_central_binom 1 n
end

-- This bound is of interest because it appears in Erdős's proof of Bertrand's postulate.
lemma four_pow_le_two_mul_n_mul_central_binom (n : ℕ) (n_pos : 0 < n) :
  4 ^ n ≤ (2 * n) * (2 * n).choose n :=
begin
  have mean_bound :
    (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)
      ≤ (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose n),
    { exact finset.sum_le_sum (λ i _, choose_le_central_binom i n), },

  have constant_sum :
    (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose n) =
      (finset.Ico 1 (2 * n)).card * (2 * n).choose n,
    { exact finset.sum_const _, },

  have n_sum : 1 + (2 * n - 1) = 2 * n :=
    nat.add_sub_of_le (one_le_mul one_le_two (succ_le_iff.mpr n_pos)),

  have split_sum : ({0} ∪ finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)
    = (finset.sum {0} (λ i, (2 * n).choose i) + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)),
    { rw finset.sum_union,
      refine finset.singleton_disjoint.mpr _,
      simp only [nat.one_ne_zero, not_false_iff, finset.mem_Ico, nonpos_iff_eq_zero, false_and], },

  have split_range :
    (finset.range (2 * n + 1)).sum (λ i, (2 * n).choose i)
      = ({0} ∪ finset.Ico 1 (2 * n) ∪ {2 * n}).sum (λi, (2 * n).choose i),
    { apply finset.sum_congr,
      { ext,
        simp only
          [finset.mem_union, finset.union_assoc, finset.mem_singleton, finset.mem_range,
          finset.mem_Ico],
        split,
        { intros a_small,
          cases le_or_lt 1 a with one_le_a a_le_one,
          { right,
            cases lt_or_le a (2 * n) with a_small a_big,
            { left, exact ⟨one_le_a, a_small⟩, },
            { right, exact eq_of_le_of_lt_succ a_big a_small, }, },
          { simp only [lt_one_iff] at a_le_one,
            left, exact a_le_one, }, },
        { intros hyp,
          rcases hyp with a_zero | ⟨_, a_small⟩,
          { subst a_zero, exact (2 * n).succ_pos, },
          { exact lt.step a_small, },
          { subst hyp, exact lt_add_one (2 * n), }, }, },
      { intros x hyp,
        simp at hyp, }, },

  calc
    4 ^ n = (2 ^ 2) ^ n : by refl
      ... = (1 + 1) ^ (2 * n) : by rw pow_mul
      ... = (finset.range (2 * n + 1)).sum (λ i, (2 * n).choose i) :
        by simp only [add_pow 1 1 (2 * n), one_pow, one_mul, cast_id]
      ... = ({0} ∪ finset.Ico 1 (2 * n) ∪ {2 * n}).sum (λi, (2 * n).choose i) : split_range
      ... = ({0} ∪ finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)
            + finset.sum {2 * n} (λi, (2 * n).choose i) :
        begin
          rw finset.sum_union,
          refine finset.disjoint_singleton.mpr _,
          simp only
            [nat.one_ne_zero, nat.mul_eq_zero, false_or, or_false, finset.right_not_mem_Ico,
            bit0_eq_zero, finset.mem_union, finset.mem_singleton],
          exact ne_of_gt n_pos,
        end
      ... = ({0} ∪ finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i) + ((2 * n).choose (2 * n)) :
        by rw finset.sum_singleton
      ... = (({0} ∪ finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)) + 1 : by rw choose_self
      ... = (finset.sum {0} (λ i, (2 * n).choose i)
              + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i))
            + 1 :
        by rw split_sum
      ... = ((2 * n).choose 0 + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)) + 1 :
        by rw finset.sum_singleton
      ... = (1 + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i)) + 1 : by rw choose_zero_right
      ... = 1 + 1 + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i) : add_right_comm 1 _ 1
      ... = 2 + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose i) : by refl
      ... ≤ 2 + (finset.Ico 1 (2 * n)).sum (λ i, (2 * n).choose n) : add_le_add_left mean_bound 2
      ... = 2 + (finset.Ico 1 (2 * n)).card * (2 * n).choose n : by rw constant_sum
      ... = 2 + (2 * n - 1) * (2 * n).choose n : by rw nat.card_Ico 1 (2 * n)
      ... ≤ (2 * n).choose n + (2 * n - 1) * (2 * n).choose n :
        add_le_add_right (two_le_central_binom n n_pos) _
      ... = (1 + (2 * n - 1)) * (2 * n).choose n :
        by rw [nat.right_distrib 1 (2 * n - 1) ((2 * n).choose n), one_mul]
      ... = (2 * n) * (2 * n).choose n : by rw n_sum,
end

lemma four_pow_n_lt_n_mul_central_binom {n : ℕ} (n_big : 4 ≤ n) : 4 ^ n < n * (2 * n).choose n :=
begin
  induction n,
  { linarith, },
  { sorry, },
end

end nat
