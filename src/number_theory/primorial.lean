/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/
import tactic
import data.nat.parity
import data.nat.choose

/-!
# Primorial

This file defines the primorial function, and proves a bound on its size.

## Notations

We use the notation `n#` for the primorial of `n`: that is, the product of the primes less than
or equal to `n`.
-/

open finset
open nat
open_locale big_operators

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ := ∏ p in (filter prime (range (n + 1))), p
local notation x`#` := primorial x

private lemma choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m :=
by apply choose_symm_of_eq_add; ring

lemma primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % 2 = 1) : (n + 1)# = n# :=
begin
  have not_prime : ¬prime (n + 1),
    { intros is_prime,
      cases (prime.eq_two_or_odd is_prime),
      { linarith, },
      { rw ←not_even_iff at h r,
        have e : even (n + 1 - n), exact (even_sub (le_of_lt (lt_add_one n))).2 (iff_of_false h r),
        exfalso,
        simp only [nat.add_sub_cancel_left, not_even_one] at e,
        exact e, }, },
  apply finset.prod_congr,
  { rw [@range_succ (n + 1), filter_insert, if_neg not_prime], },
  { exact λ _ _, rfl, },
end

private lemma range_contains_upper_bound (n : ℕ) : n ∈ range (n + 1) :=
by simp only [succ_pos', lt_add_iff_pos_right, mem_range]

private lemma select_from_sum (f : ℕ → ℕ) (s : finset ℕ) (a : ℕ) (t : a ∈ s) : f a ≤ ∑ i in s, f i :=
by rw <- finset.insert_erase t; simp

private lemma bound_binomial_coefficient (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n :=
begin
  have t : choose (2 * n + 1) n ≤ ∑ i in range (n + 1), choose (2 * n + 1) i,
    exact select_from_sum (choose (2 * n + 1)) (range (n + 1)) n (range_contains_upper_bound n),
  simpa [sum_range_choose_halfway n] using t
end

lemma dvd_choose_of_middling_prime (p : ℕ) (is_prime : prime p) (m : ℕ)
  (p_big : m + 1 < p) (p_small : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) (m + 1) :=
begin
  have m_size : m + 1 ≤ 2 * m + 1, by exact le_of_lt (lt_of_lt_of_le p_big p_small),
  let e := @choose_mul_fact_mul_fact (2 * m + 1) (m + 1) m_size,
  have r : p ∣ nat.fact (2 * m + 1), exact (prime.dvd_fact is_prime).mpr p_small,
  have s : (p ∣ nat.fact (m + 1)) → false,
    { intros,
      let e := (prime.dvd_fact is_prime).mp a,
      linarith, },
  have t : (p ∣ nat.fact (2 * m + 1 - (m + 1))) → false,
    { intros,
      let f := (prime.dvd_fact is_prime).mp a,
      have t : 2 * m + 1 - (m + 1) = m, { norm_num, rw two_mul m, exact nat.add_sub_cancel m m, },
      rw t at f,
      clear t a s r p_small is_prime e m_size,
      cases lt_trichotomy p m,
      { have r : m < m + 1, exact lt_add_one m, linarith, },
      { cases h,
        { rw h at p_big,
          linarith, },
        linarith, }, },
  rw [←e, mul_assoc] at r,
  cases (prime.dvd_mul is_prime).1 r,
  { exact h, },
  cases (prime.dvd_mul is_prime).1 h,
  cc, cc,
end

lemma prod_primes_dvd {s : finset ℕ} : ∀ (n : ℕ) (h : ∀ a ∈ s, prime a) (div : ∀ a ∈ s, a ∣ n),
  (∏ p in s, p) ∣ n :=
begin
  apply finset.induction_on s,
  { simp, },
  { intros a s a_not_in_s induct,
    intros n primes divs,
    rw finset.prod_insert a_not_in_s,
    have a_div_n : a ∣ n, { exact divs a (finset.mem_insert_self a s) },
    rcases a_div_n with ⟨ k, k_times ⟩,
    rw k_times,
    have step : ∏ p in s, p ∣ k,
      { apply induct k,
        { intros b b_in_s,
          exact primes b (finset.mem_insert_of_mem b_in_s), },
        { intros b b_in_s,
          have b_div_n, by exact divs b (finset.mem_insert_of_mem b_in_s),
          have a_prime : prime a, { exact primes a (finset.mem_insert_self a s), },
          have b_prime : prime b, { exact primes b (finset.mem_insert_of_mem b_in_s), },
          rw k_times at b_div_n,
          have r : b ∣ a ∨ b ∣ k, exact (prime.dvd_mul b_prime).mp b_div_n,
          cases r with b_div_a b_div_k,
          { exfalso,
            have b_eq_a : b = a,
            { cases (nat.dvd_prime a_prime).1 b_div_a with b_eq_1 b_eq_a,
              { subst b_eq_1, exfalso, exact prime.ne_one b_prime rfl, },
              { exact b_eq_a } },
            subst b_eq_a,
            exact a_not_in_s b_in_s, },
          { exact b_div_k } } },
    exact mul_dvd_mul_left a step, }
end

lemma primorial_le_pow_4 : ∀ (n : ℕ), n# ≤ 4 ^ n
| 0 := le_refl _
| 1 := le_of_inf_eq rfl
| (n + 2) :=
  match nat.mod_two_eq_zero_or_one (n + 1) with
  | or.inl n_odd :=
    match nat.even_iff.2 n_odd with
    | ⟨m, twice_m⟩ :=
      let recurse : m + 1 < n + 2 := by linarith in
      by { calc (n + 2)#
          = ∏ i in filter prime (range (2 * m + 2)), i : by simpa [←twice_m]
      ... = ∏ i in filter prime (finset.Ico (m + 2) (2 * m + 2) ∪ range (m + 2)), i :
            by
            { rw [range_eq_Ico, range_eq_Ico, finset.union_comm, finset.Ico.union_consecutive],
              exact bot_le,
              simp only [add_le_add_iff_right],
              linarith, }
      ... = ∏ i in (filter prime (finset.Ico (m + 2) (2 * m + 2)) ∪ (filter prime (range (m + 2)))), i :
            by rw filter_union
      ... = (∏ i in filter prime (finset.Ico (m + 2) (2 * m + 2)), i)
            * (∏ i in filter prime (range (m + 2)), i) :
            by
            { apply finset.prod_union,
              have u : disjoint (finset.Ico (m + 2) (2 * m + 2)) (range (m + 2)),
              { simp only [finset.disjoint_left, and_imp, finset.Ico.mem, not_lt, finset.mem_range],
                intros _ pr _, exact pr, },
              exact finset.disjoint_filter_filter u, }
      ... ≤ (∏ i in filter prime (finset.Ico (m + 2) (2 * m + 2)), i) * 4 ^ (m + 1) :
            by
            { have r : (m + 1)# ≤ 4 ^ (m + 1),
              { have m_nonzero : 0 < m, by linarith,
                exact primorial_le_pow_4 (m + 1), },
              exact nat.mul_le_mul_left _ r, }
      ... ≤ (choose (2 * m + 1) (m + 1)) * 4 ^ (m + 1) :
            by
            { have s : ∏ i in filter prime (finset.Ico (m + 2) (2 * m + 2)), i ∣ choose (2 * m + 1) (m + 1),
              { refine prod_primes_dvd  (choose (2 * m + 1) (m + 1)) _ _,
                { intros a, rw finset.mem_filter, cc, },
                { intros a, rw finset.mem_filter,
                  intros pr,
                  rcases pr with ⟨ size, is_prime ⟩,
                  simp only [finset.Ico.mem] at size,
                  rcases size with ⟨ a_big , a_small ⟩,
                  exact dvd_choose_of_middling_prime a is_prime m a_big (nat.lt_succ_iff.mp a_small), }, },
              have r : ∏ i in filter prime (finset.Ico (m + 2) (2 * m + 2)), i ≤ choose (2 * m + 1) (m + 1),
                { refine @nat.le_of_dvd _ _ _ s,
                  exact @choose_pos (2 * m + 1) (m + 1) (by linarith), },
              exact nat.mul_le_mul_right _ r, }
      ... = (choose (2 * m + 1) m) * 4 ^ (m + 1) : by rw choose_symm_half m
      ... ≤ 4 ^ m * 4 ^ (m + 1) : nat.mul_le_mul_right _ (bound_binomial_coefficient m)
      ... = 4 ^ (m + (m + 1)) : eq.symm (nat.pow_add 4 m (m + 1))
      ... = 4 ^ ((m + m) + 1) : by rw add_assoc m m 1
      ... = 4 ^ (2 * m + 1) : by ring
      ... = 4 ^ (n + 2) : by rw ←twice_m, }
    end
  | or.inr n_even :=
    by { cases lt_trichotomy 1 (n + 1) with one_lt_n n_lt_one,
      { rw primorial_succ (by linarith) n_even,
        calc (n + 1)#
              ≤ 4 ^ n.succ : primorial_le_pow_4 (n + 1)
          ... ≤ 4 ^ (n + 2) : nat.le_add_left _ _, },
      cases n_lt_one,
      { cases lt_trichotomy 0 n,
        { exfalso, linarith, },
        { cases h,
          { rw ←h,
            norm_num,
            have r : 2# = 2, by refl,
            rw r,
            norm_num, },
          linarith, }, },
      { have e : n < 0, exact nat.lt_of_succ_lt_succ n_lt_one,
        interval_cases n, }, }

end
