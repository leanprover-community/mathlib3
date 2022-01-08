/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/
import tactic.ring_exp
import data.nat.parity
import data.nat.choose.sum

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
  have not_prime : ¬nat.prime (n + 1),
  { intros is_prime,
    cases (prime.eq_two_or_odd is_prime) with _ n_even,
    { linarith, },
    { apply nat.zero_ne_one,
      rwa [add_mod, r, nat.one_mod, ←two_mul, mul_one, nat.mod_self] at n_even, }, },
  apply finset.prod_congr,
  { rw [@range_succ (n + 1), filter_insert, if_neg not_prime], },
  { exact λ _ _, rfl, },
end

lemma dvd_choose_of_middling_prime (p : ℕ) (is_prime : nat.prime p) (m : ℕ)
  (p_big : m + 1 < p) (p_small : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) (m + 1) :=
begin
  have m_size : m + 1 ≤ 2 * m + 1 := le_of_lt (lt_of_lt_of_le p_big p_small),
  have s : ¬(p ∣ (m + 1)!),
  { intros p_div_fact,
    have p_le_succ_m : p ≤ m + 1 := (prime.dvd_factorial is_prime).mp p_div_fact,
    linarith, },
  have t : ¬(p ∣ (2 * m + 1 - (m + 1))!),
  { intros p_div_fact,
    have p_small : p ≤ 2 * m + 1 - (m + 1) := (prime.dvd_factorial is_prime).mp p_div_fact,
    linarith, },
  have expanded :
    choose (2 * m + 1) (m + 1) * (m + 1)! * (2 * m + 1 - (m + 1))! = (2 * m + 1)! :=
    @choose_mul_factorial_mul_factorial (2 * m + 1) (m + 1) m_size,
  have p_div_big_fact : p ∣ (2 * m + 1)! := (prime.dvd_factorial is_prime).mpr p_small,
  rw [←expanded, mul_assoc] at p_div_big_fact,
  obtain p_div_choose | p_div_facts : p ∣ choose (2 * m + 1) (m + 1) ∨ p ∣ _! * _! :=
    (prime.dvd_mul is_prime).1 p_div_big_fact,
  { exact p_div_choose, },
  cases (prime.dvd_mul is_prime).1 p_div_facts,
  cc, cc,
end

lemma prod_primes_dvd {s : finset ℕ} : ∀ (n : ℕ) (h : ∀ a ∈ s, nat.prime a) (div : ∀ a ∈ s, a ∣ n),
  (∏ p in s, p) ∣ n :=
begin
  apply finset.induction_on s,
  { simp, },
  { intros a s a_not_in_s induct n primes divs,
    rw finset.prod_insert a_not_in_s,
    obtain ⟨k, rfl⟩ : a ∣ n := divs a (finset.mem_insert_self a s),
    apply mul_dvd_mul_left a,
    apply induct k,
    { intros b b_in_s,
      exact primes b (finset.mem_insert_of_mem b_in_s), },
    { intros b b_in_s,
      have b_div_n := divs b (finset.mem_insert_of_mem b_in_s),
      have a_prime := primes a (finset.mem_insert_self a s),
      have b_prime := primes b (finset.mem_insert_of_mem b_in_s),
      refine ((prime.dvd_mul b_prime).mp b_div_n).resolve_left (λ b_div_a, _),
      obtain rfl : b = a := ((nat.dvd_prime a_prime).1 b_div_a).resolve_left b_prime.ne_one,
      exact a_not_in_s b_in_s, } },
end

lemma primorial_le_4_pow : ∀ (n : ℕ), n# ≤ 4 ^ n
| 0 := le_refl _
| 1 := le_of_inf_eq rfl
| (n + 2) :=
  match nat.mod_two_eq_zero_or_one (n + 1) with
  | or.inl n_odd :=
    match nat.even_iff.2 n_odd with
    | ⟨m, twice_m⟩ :=
      let recurse : m + 1 < n + 2 := by linarith in
      begin
        calc (n + 2)#
            = ∏ i in filter nat.prime (range (2 * m + 2)), i : by simpa [←twice_m]
        ... = ∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2) ∪ range (m + 2)), i :
              begin
                rw [range_eq_Ico, finset.union_comm, finset.Ico_union_Ico_eq_Ico],
                exact bot_le,
                simp only [add_le_add_iff_right],
                linarith,
              end
        ... = ∏ i in (filter nat.prime (finset.Ico (m + 2) (2 * m + 2))
              ∪ (filter nat.prime (range (m + 2)))), i :
              by rw filter_union
        ... = (∏ i in filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i)
              * (∏ i in filter nat.prime (range (m + 2)), i) :
              begin
                apply finset.prod_union,
                have disj : disjoint (finset.Ico (m + 2) (2 * m + 2)) (range (m + 2)),
                { simp only [finset.disjoint_left, and_imp, finset.mem_Ico, not_lt,
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
                  { intros a, rw finset.mem_filter, cc, },
                  { intros a, rw finset.mem_filter,
                    intros pr,
                    rcases pr with ⟨ size, is_prime ⟩,
                    simp only [finset.mem_Ico] at size,
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
        ... = 4 ^ (n + 2) : by rw ←twice_m,
      end
    end
  | or.inr n_even :=
    begin
      obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := lt_or_le 1 (n + 1),
      { rw primorial_succ (by linarith) n_even,
        calc (n + 1)#
              ≤ 4 ^ n.succ : primorial_le_4_pow (n + 1)
          ... ≤ 4 ^ (n + 2) : pow_le_pow (by norm_num) (nat.le_succ _), },
      { have n_zero : n = 0 := eq_bot_iff.2 (succ_le_succ_iff.1 n_le_one),
        norm_num [n_zero, primorial, range_succ, prod_filter, nat.not_prime_zero, nat.prime_two] },
    end

end
