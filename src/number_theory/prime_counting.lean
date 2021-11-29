/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime
import tactic.interval_cases
import tactic.cancel_denoms
import tactic.linarith
import data.nat.totient
import data.multiset.locally_finite
import algebra.periodic


/-!
# The Prime Counting Function

In this file we define the prime counting function - the function on natural numbers that returns
the number of primes less than or equal to its input.
-/

namespace nat
open finset

/--
A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.
-/
def prime_counting' (n : ℕ) : ℕ := ((range n).filter (prime)).card

/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def prime_counting (n : ℕ) : ℕ := ((range (n + 1)).filter (prime)).card

localized "notation `π` := nat.prime_counting" in nat
localized "notation `π'` := nat.prime_counting'" in nat


-- lemma filter_mod_eq_range_card (a b n : ℕ) :
--   (filter (λ (i : ℕ), i % a = b) (range n)).card = (n - b) / a :=
-- begin
--   sorry,
-- end

lemma monotone_prime_counting : monotone prime_counting :=
begin
  intros a b a_le_b,
  unfold prime_counting,
  apply card_le_of_subset,
  apply monotone_filter_left,
  simp only [le_eq_subset, range_subset, add_le_add_iff_right],
  exact a_le_b,
end

lemma monotone_prime_counting' : monotone prime_counting' :=
begin
  intros a b a_le_b,
  unfold prime_counting',
  apply card_le_of_subset,
  apply monotone_filter_left,
  simp only [le_eq_subset, range_subset],
  exact a_le_b,
end

lemma split_range {n k : ℕ} (k_le_n : k ≤ n) (p : ℕ -> Prop) [decidable_pred p]
  : (range n).filter p = (range k).filter p ∪ (Ico k n).filter p :=
begin
  rw <- filter_union,
  ext,
  simp only [mem_union, mem_filter, mem_range, and.congr_left_iff, mem_Ico],
  intro _,
  split,
  { intros a_le_n,
    cases lt_or_le a k,
    { left, exact h, },
    { right, exact ⟨h, a_le_n⟩, }, },
  { intros hyp,
    cases hyp,
    { exact gt_of_ge_of_gt k_le_n hyp, },
    { exact hyp.2, }, },
end

lemma eq_or_coprime_of_lt_prime {n k : ℕ} (h0 : 0 < n) (hlt : n ≤ k) (is_prime : prime k) :
  k = n ∨ coprime k n :=
begin
  sorry,
end


example (a b : ℕ) (h : a ≠ b) : a ≤ b ↔ a < b := ne.le_iff_lt h

lemma Ico_eq_insert_Ico_succ (a b : ℕ) (h : a < b) : Ico a b = insert a (Ico a.succ b) :=
begin
  rw Ico_succ_left,
  rw ext_iff,
  intro a_1,
  simp only [mem_Ico, mem_Ioo, mem_insert],
  by_cases h2 : a_1 = a,
  { simp [h2, h], },
  { simp [h2],
    intro h3,
    exact (ne.symm h2).le_iff_lt,},
end

-- TODO Generalize from ℕ to any (ordered add monoid?)
lemma filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ -> Prop) [decidable_pred p]
 (pp : function.periodic p a) :
  (filter p (Ico n (n+a))).card = (filter p (Ico 0 a)).card :=
begin
  by_cases a = 0,
  { simp [h], },
  induction n,
  { simp, },
  { rw <-n_ih,
    clear n_ih,
    simp only [succ_add],
    -- Cast to multisets?
    rw Ico_succ_right_eq_insert_Ico,
    rw Ico_succ_left_eq_erase_Ico,
    rw filter_insert,
    rw filter_erase,
    split_ifs,
    { rw card_insert_eq_ite,
      rw card_erase_eq_ite,
      rw pp at h_1,
      split_ifs,
      simp [*] at *,
      rw add_one,
      rw succ_pred_eq_of_pos,
      rw card_pos,

      rw finset.nonempty,
      use n_n,
      assumption,

      simp [mem_filter] at *,
      have a_pos : 0 < a, exact pos_iff_ne_zero.mpr h,
      exact h_3 a_pos h_1 },
    { rw card_erase_eq_ite,
      split_ifs,
      simp [*] at *, },
    rw succ_eq_add_one,
    simp,
    exact one_le_iff_ne_zero.mpr h, },
end

@[simp]
lemma coprime_add_iff_coprime (a b : ℕ) : coprime a (a + b) ↔ coprime a b :=
begin
  rw coprime,
  rw coprime,
  rw [gcd_rec],
  simp,
  rw <-gcd_rec,
end


lemma filter_mod_eq_range_card (a n : ℕ) :
  (filter (a.coprime) (Ico n (n+a))).card = totient a :=
begin
  rw totient,
  symmetry,
  have h := filter_Ico_card_eq_of_periodic n a,
  simp at h,
  rw h,
  intro x,
  rw add_comm,
  exact coprime_add_iff_coprime a x,
end

lemma filter_coprime_bound (a n : ℕ) (a_pos : 0 < a) :
  (filter (a.coprime) (Ico a n)).card ≤ totient a * (n / a) :=
begin
  conv
  begin
    to_lhs,
    rw <-nat.mod_add_div n a,
  end,
  induction n / a,
  { simp [le_of_lt (mod_lt n a_pos)], },
  { simp only [mul_succ],
    rw <-add_assoc,
    suffices : (filter a.coprime (Ico a (n % a + a * n_1 + a))).card
        ≤ (filter a.coprime (Ico a (n % a + a * n_1))).card + a.totient,
    { exact le_add_of_le_add_right this ih, },
    calc (filter a.coprime (Ico a (n % a + a * n_1 + a))).card
        ≤ (filter a.coprime (Ico a (n % a + a * n_1)
                              ∪ Ico (n % a + a * n_1) (n % a + a * n_1 + a))).card :
          begin
            apply card_le_of_subset,
            apply monotone_filter_left,
            -- let b := n % a + a * n_1,
            -- rw <-b,
            simp only [finset.le_eq_subset],
            rw subset_iff,
            intro x,
            simp [mem_Ico],
            intros h1 h2,
            by_cases x < n % a + a * n_1,
            { left,
              exact ⟨h1, h⟩, },
            { right,
              exact ⟨le_of_not_lt h, h2⟩, },
          end
    ... ≤ (filter a.coprime (Ico a (n % a + a * n_1))).card + a.totient :
          begin
            rw filter_union,
            rw <-filter_mod_eq_range_card a (n % a + a * n_1),
            apply card_union_le,
          end },
end

-- TODO remove h0 h1 k_le_n assumption
/-- A linear upper bound on the size of the `prime_counting'` function -/
lemma linear_prime_counting_bound (n k : ℕ) (h0 : 0 < k) (k_lt_n : k < n) (k_le_n : k ≤ n) :
  π' n ≤ π' k + 1 + nat.totient k * (n / k) :=
calc π' n ≤ ((range k).filter (prime)).card + ((Ico k n).filter (prime)).card :
            begin
              rw [prime_counting', split_range k_le_n],
              apply card_union_le,
            end
     ... ≤ π' k + ((Ico k n).filter (prime)).card : by rw prime_counting'
     ... ≤ π' k + ((Ico k n).filter (λ i, i = k ∨ coprime k i)).card :
            begin
              apply add_le_add_left,
              apply card_le_of_subset,
              rw subset_iff,
              simp,
              intros p succ_k_le_p p_lt_n p_prime,
              -- have k_lt_p : k < p, linarith,
              split,
              { exact ⟨succ_k_le_p, p_lt_n⟩, },
              { rw coprime_comm,
                apply eq_or_coprime_of_lt_prime h0 _ p_prime,
                exact succ_k_le_p, },
            end
     ... ≤ π' k + ({k} ∪ filter (λ (a : ℕ), k.coprime a) (Ico k n)).card :
            begin
              apply add_le_add_left,
              rw [filter_or, filter_eq'],
              simp,
              rw if_pos k_lt_n,
            end
      ... ≤ π' k + (1 + nat.totient k * (n / k)) :
            begin
              apply add_le_add_left,
              apply trans (card_union_le {k} (filter (λ (a : ℕ), k.coprime a) (Ico k n))),
              simp only [add_le_add_iff_left, card_singleton],
              exact filter_coprime_bound k n h0,
            end
    ... = π' k + 1 + nat.totient k * (n / k) : by rw [add_assoc]


end nat
