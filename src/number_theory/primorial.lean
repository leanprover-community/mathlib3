/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/
import algebra.big_operators.associated
import data.nat.choose.sum
import data.nat.parity
import tactic.ring_exp

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

open finset
open nat
open_locale big_operators nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ := ∏ p in (filter nat.prime (range (n + 1))), p
local notation x`#` := primorial x

lemma primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % 2 = 1) : (n + 1)# = n# :=
begin
  refine prod_congr _ (λ _ _, rfl),
  rw [range_succ, filter_insert, if_neg (λ h, _)],
  have two_dvd : 2 ∣ n + 1 := dvd_iff_mod_eq_zero.mpr (by rw [← mod_add_mod, r, mod_self]),
  linarith [(h.dvd_iff_eq (nat.bit0_ne_one 1)).mp two_dvd],
end

lemma dvd_choose_of_middling_prime (p : ℕ) (is_prime : nat.prime p) (m : ℕ)
  (p_big : m + 1 < p) (p_small : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) (m + 1) :=
begin
  have m_size : m + 1 ≤ 2 * m + 1 := le_of_lt (lt_of_lt_of_le p_big p_small),
  have s : ¬(p ∣ (m + 1)!),
  { intros p_div_fact,
    exact lt_le_antisymm p_big (is_prime.dvd_factorial.mp p_div_fact), },
  have t : ¬(p ∣ (2 * m + 1 - (m + 1))!),
  { intros p_div_fact,
    refine lt_le_antisymm (lt_of_succ_lt p_big) _,
    convert is_prime.dvd_factorial.mp p_div_fact,
    rw [two_mul, add_assoc, nat.add_sub_cancel] },
  have expanded :
    choose (2 * m + 1) (m + 1) * (m + 1)! * (2 * m + 1 - (m + 1))! = (2 * m + 1)! :=
    @choose_mul_factorial_mul_factorial (2 * m + 1) (m + 1) m_size,
  have p_div_big_fact : p ∣ (2 * m + 1)! := (prime.dvd_factorial is_prime).mpr p_small,
  rw [←expanded, mul_assoc] at p_div_big_fact,
  obtain p_div_choose | p_div_facts : p ∣ choose (2 * m + 1) (m + 1) ∨ p ∣ _! * _! :=
    (prime.dvd_mul is_prime).1 p_div_big_fact,
  { exact p_div_choose, },
  cases (prime.dvd_mul is_prime).1 p_div_facts,
  exacts [(s h).elim, (t h).elim],
end

lemma primorial_le_4_pow : ∀ (n : ℕ), n# ≤ 4 ^ n
| 0 := le_rfl
| 1 := le_of_inf_eq rfl
| (n + 2) :=
  match nat.mod_two_eq_zero_or_one (n + 1) with
  | or.inl n_odd :=
    match nat.even_iff.2 n_odd with
    | ⟨m, twice_m⟩ :=
      have recurse : m + 1 < n + 2 := by linarith,
      begin
        calc (n + 2)#
            = ∏ i in filter nat.prime (range (2 * m + 2)), i : by simpa [two_mul, ←twice_m]
        ... = ∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2) ∪ range (m + 2)), i :
              begin
                rw [range_eq_Ico, finset.union_comm, finset.Ico_union_Ico_eq_Ico],
                { exact bot_le },
                { simpa only [add_le_add_iff_right, two_mul] using nat.le_add_left m m },
              end
        ... = ∏ i in (filter nat.prime (finset.Ico (m + 2) (2 * m + 2))
              ∪ (filter nat.prime (range (m + 2)))), i :
              by rw filter_union
        ... = (∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i)
              * (∏ i in filter nat.prime (range (m + 2)), i) :
              begin
                apply finset.prod_union,
                have disj : disjoint (finset.Ico (m + 2) (2 * m + 2)) (range (m + 2)),
                { simv only [finset.disjoint_left, and_imp, finset.mem_Ico, not_lt,
                    finset.mem_range],
                  intros _ pr _, exact pr, },
                exact finset.disjoint_filter_filter disj,
              end
        ... ≤ (∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i) * 4 ^ (m + 1) :
              nat.mul_le_mul_left _ (primorial_le_4_pow (m + 1))
        ... ≤ (choose (2 * m + 1) (m + 1)) * 4 ^ (m + 1) :
              begin
                have s : ∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2)),
                  i ∣ choose (2 * m + 1) (m + 1),
                { refine prod_primes_dvd  (choose (2 * m + 1) (m + 1)) _ _,
                  { intros a, rw [finset.mem_filter, nat.prime_iff], apply and.right, },
                  { intros a, rw finset.mem_filter,
                    intros pr,
                    rcases pr with ⟨ size, is_prime ⟩,
                    simv only [finset.mem_Ico] at size,
                    rcases size with ⟨ a_big , a_small ⟩,
                    exact dvd_choose_of_middling_prime a is_prime m a_big
                      (nat.lt_succ_iff.mp a_small), }, },
                have r : ∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2)),
                  i ≤ choose (2 * m + 1) (m + 1),
                { refine @nat.le_of_dvd _ _ _ s,
                  exact @choose_pos (2 * m + 1) (m + 1) (by linarith), },
                exact nat.mul_le_mul_right _ r,
              end
        ... = (choose (2 * m + 1) m) * 4 ^ (m + 1) : by rw choose_symm_half m
        ... ≤ 4 ^ m * 4 ^ (m + 1) : nat.mul_le_mul_right _ (choose_middle_le_pow m)
        ... = 4 ^ (2 * m + 1) : by ring_exp
        ... = 4 ^ (n + 2) : by rw [two_mul, ←twice_m],
      end
    end
  | or.inr n_even :=
    begin
      obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := lt_or_le 1 (n + 1),
      { rw primorial_succ one_lt_n n_even,
        calc (n + 1)#
              ≤ 4 ^ n.succ : primorial_le_4_pow (n + 1)
          ... ≤ 4 ^ (n + 2) : pow_le_pow (by norm_num) (nat.le_succ _), },
      { have n_zero : n = 0 := eq_bot_iff.2 (succ_le_succ_iff.1 n_le_one),
        norm_num [n_zero, primorial, range_succ, prod_filter, nat.not_prime_zero, nat.prime_two] },
    end

end
