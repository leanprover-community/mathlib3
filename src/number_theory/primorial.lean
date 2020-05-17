import data.list import data.nat.prime
import data.nat.choose
import algebra.euclidean_domain
import algebra.big_operators
import tactic

open_locale big_operators

-- This is going into stdlib
lemma sum_range_choose_halfway (m : nat) : ∑ i in finset.range (m + 1), nat.choose (2 * m + 1) i = 4 ^ m :=
   by sorry

private lemma add_one_zero (a : nat) (p : a + 1 = 0) : false := by linarith

lemma choose_symmetric
  (m : nat)
  : nat.choose (2 * m + 1) (m + 1) = nat.choose (2 * m + 1) m
  :=
begin
  apply nat.choose_symm_of_eq_add,
  ring,
end

lemma extend_prime_product_odd
  (n : nat)
  (n_big : 2 < n)
  (r : n % 2 = 0)
  : ∏ i in (finset.filter nat.prime (finset.range n)), i = ∏ i in (finset.filter nat.prime (finset.range (n + 1))), i
  :=
begin
  have not_prime : nat.prime n → false,
  {
    intros is_prime,
    cases (nat.prime.eq_two_or_odd is_prime),
    { subst h, linarith, },
    { linarith }
  },
  have t :
    ∏ i in (finset.filter nat.prime (finset.range n.succ)), i
    = (∏ i in (finset.filter nat.prime (finset.range n)), i) * (if nat.prime n then n else 1),
  {
    have s : finset.range n.succ = insert n (finset.range n), by exact finset.range_succ,
    rw [s, finset.filter_insert, if_neg not_prime, if_neg not_prime],
    ring,
  },
  rw t,
  simp only [not_prime, mul_one, if_false],
end

private lemma range_contains_upper_bound (n : nat) : n ∈ finset.range n.succ :=
begin
  suffices : (n < n + 1), by simpa,
  exact lt_add_one n,
end

lemma select_from_sum (f : nat → nat) (s : finset nat) (a : nat) (t : a ∈ s) : f a ≤ ∑ i in s, f i :=
begin
  rw <- finset.insert_erase t,
  simp,
end

lemma bound_binomial_coefficient (n : nat) : nat.choose (2 * n + 1) n ≤ 4 ^ n :=
begin
  have t : nat.choose (2 * n + 1) n ≤ ∑ i in finset.range (n + 1), nat.choose (2 * n + 1) i,
    exact select_from_sum (nat.choose (2 * n + 1)) (finset.range (n + 1)) n (range_contains_upper_bound n),
  simpa [sum_range_choose_halfway n] using t
end

private lemma can_halve : ∀ (m : nat), (m % 2 = 0) → ∃ n, 2 * n = m
| 0 := λ _, ⟨ 0, rfl ⟩
| 1 := λ one_even, by {exfalso, norm_num at one_even}
| (nat.succ (nat.succ m)) := λ is_even, by {
  rcases can_halve m is_even with ⟨ half, is_half ⟩,
  use (half + 1),
  ring,
  subst is_half,
}

private lemma halving_wellfounded (m n : nat) (pr : 2 * m = n + 1) (m_big : 0 < m) : m + 1 < n.succ.succ :=
begin
  have u : n.succ.succ = (n + 1) + 1, by norm_num,
  rw u,
  rw <- pr,
  simp only [add_lt_add_iff_right],
  linarith,
end

private lemma increment_bit : ∀ (m : nat), (m % 2 = 1) → m.succ % 2 = 0
| 0 := λ pr, by norm_num at pr
| 1 := λ pr, by norm_num
| (nat.succ (nat.succ m)) := λ pr, by
begin
  rw nat.mod_def _ 2,
  simp only [true_and, nat.succ_pos', nat.succ_sub_succ_eq_sub, nat.sub_zero],
  rw increment_bit m (by exact pr),
  rw if_pos,
  exact sup_eq_left.mp rfl,
end

lemma succ_not_lt (m : nat) : m.succ < m → false :=
begin
  intros pr,
  induction m, {norm_num at pr}, {exact m_ih (nat.lt_of_succ_lt_succ pr)},
end

lemma middling_prime_divides_binom
  (p : nat)
  (is_prime : nat.prime p)
  (m : nat)
  (p_big : m.succ < p)
  (p_small : p ≤ 2 * m + 1)
  : p ∣ nat.choose (2 * m + 1) m.succ
  :=
begin
  have m_size : m.succ ≤ 2 * m + 1, by exact le_of_lt (lt_of_lt_of_le p_big p_small),
  let e := @nat.choose_mul_fact_mul_fact (2 * m + 1) m.succ m_size,
  have r : p ∣ nat.fact (2 * m + 1), exact (nat.prime.dvd_fact is_prime).mpr p_small,
  have s : (p ∣ nat.fact m.succ) → false, {
    intros,
    let e := (nat.prime.dvd_fact is_prime).mp a,
    linarith,
  },
  have t : (p ∣ nat.fact (2 * m + 1 - m.succ)) → false, {
    intros,
    let f := (nat.prime.dvd_fact is_prime).mp a,
    have t : 2 * m + 1 - m.succ = m, { norm_num, rw two_mul m, exact nat.add_sub_cancel m m, },
    rw t at f,
    clear t a s r p_small is_prime e m_size,
    cases lt_trichotomy p m,
    {have r : m < m.succ, exact lt_add_one m, linarith},
    cases h, {rw h at p_big, exact succ_not_lt m p_big}, linarith,
  },
  rw <- e at r,
  rw mul_assoc at r,
  cases (nat.prime.dvd_mul is_prime).1 r,
  {exact h},
  cases (nat.prime.dvd_mul is_prime).1 h with h h,
  cc, cc,
end

lemma primes_divide (s : finset nat) : ∀ (n : nat) (p : ∀ a ∈ s, nat.prime a) (div : ∀ a ∈ s, a ∣ n),
  (∏ i in s, i) ∣ n :=
begin
  apply finset.induction_on s,
  { simp, },
  { intros a s a_not_in_s induct,
    intros n primes divs,
    rw finset.prod_insert a_not_in_s,
    have a_div_n : a ∣ n, { exact divs a (finset.mem_insert_self a s) },
    rcases a_div_n with ⟨ k, k_times ⟩,
    rw k_times,
    have step : ∏ x in s, x ∣ k,
      { apply induct k,
        { intros b b_in_s,
          exact primes b (finset.mem_insert_of_mem b_in_s), },
        { intros b b_in_s,
          have b_div_n, by exact divs b (finset.mem_insert_of_mem b_in_s),
          have a_prime : nat.prime a, { exact primes a (finset.mem_insert_self a s), },
          have b_prime : nat.prime b, { exact primes b (finset.mem_insert_of_mem b_in_s), },
          rw k_times at b_div_n,
          have r : b ∣ a ∨ b ∣ k, exact (nat.prime.dvd_mul b_prime).mp b_div_n,
          cases r with b_div_a b_div_k,
          { exfalso,
            have b_eq_a : b = a,
            { cases (nat.dvd_prime a_prime).1 b_div_a with b_eq_1 b_eq_a,
              { subst b_eq_1, exfalso, exact nat.prime.ne_one b_prime rfl, },
              { exact b_eq_a } },
            subst b_eq_a,
            exact a_not_in_s b_in_s, },
          { exact b_div_k } } },
    exact mul_dvd_mul_left a step, }
end

lemma product_primes_bound : ∀ (n : nat), ∏ i in (finset.filter nat.prime (finset.range (n + 1))), i ≤ 4 ^ n
| 0 := le_refl _
| 1 := le_of_inf_eq rfl
| (nat.succ (nat.succ n)) :=
begin
  cases nat.mod_two_eq_zero_or_one n.succ,
  {
    rcases (can_halve (n + 1) h) with ⟨ m , twice_m ⟩,
    calc (∏ i in finset.filter nat.prime (finset.range n.succ.succ.succ), i)
          = ∏ i in finset.filter nat.prime (finset.range (2 * m + 2)), i : by rw twice_m
      ... = ∏ i in finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2) ∪ finset.range (m + 2)), i :
      by {
        rw finset.range_eq_Ico,
        rw finset.range_eq_Ico,
        rw finset.union_comm,
        rw finset.Ico.union_consecutive,
        exact bot_le,
        have u : m ≤ 2 * m, linarith,
        simp only [add_le_add_iff_right], exact u,
      }
      ... = ∏ i in (finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2)) ∪ (finset.filter nat.prime (finset.range (m + 2)))), i :
        by rw finset.filter_union
      ... = (∏ i in finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i)
            * (∏ i in finset.filter nat.prime (finset.range (m + 2)), i) : by {
              apply finset.prod_union,
              have u : disjoint (finset.Ico (m + 2) (2 * m + 2)) (finset.range (m + 2)), {
                simp only [finset.disjoint_left, and_imp, finset.Ico.mem, not_lt, finset.mem_range],
                intros _ pr _, exact pr
              },
              exact finset.disjoint_filter_filter u,
            }
      ... ≤ (∏ i in finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i) * 4 ^ (m + 1) : by {
        have r : ∏ i in finset.filter nat.prime (finset.range (m + 2)), i ≤ 4 ^ (m + 1),
          {
            have m_nonzero : 0 < m, by linarith,
            have recurse : m + 1 < n.succ.succ, exact halving_wellfounded m n twice_m m_nonzero,
            exact product_primes_bound (m + 1),
          },
        exact nat.mul_le_mul_left _ r,
      }
      ... ≤ (nat.choose (2 * m + 1) (m + 1)) * 4 ^ (m + 1) : by {
        have s : ∏ i in finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i ∣ nat.choose (2 * m + 1) (m + 1), {
          -- each of these primes divides the binomial coefficient, middling_prime_divides_binom
          refine primes_divide _ (nat.choose (2 * m + 1) (m + 1)) _ _,
          { intros a, rw finset.mem_filter, cc, },
          {
            intros a, rw finset.mem_filter,
            intros pr,
            rcases pr with ⟨ size, is_prime ⟩,
            simp only [finset.Ico.mem] at size,
            rcases size with ⟨ a_big , a_small ⟩,
            exact middling_prime_divides_binom a is_prime m a_big (nat.lt_succ_iff.mp a_small),
          }
        },
        have r : ∏ i in finset.filter nat.prime (finset.Ico (m + 2) (2 * m + 2)), i ≤ nat.choose (2 * m + 1) (m + 1), {
          refine @nat.le_of_dvd _ _ _ s,
          exact @nat.choose_pos (2 * m + 1) (m + 1) (by linarith),
        },
        exact nat.mul_le_mul_right _ r,
      }
      ... = (nat.choose (2 * m + 1) m) * 4 ^ (m + 1) : by rw choose_symmetric m
      ... ≤ 4 ^ m * 4 ^ (m + 1) : nat.mul_le_mul_right _ (bound_binomial_coefficient m)
      ... = 4 ^ (m + (m + 1)) : eq.symm (nat.pow_add 4 m (m + 1))
      ... = 4 ^ ((m + m) + 1) : by rw add_assoc m m 1
      ... = 4 ^ (2 * m + 1) : by ring
      ... = 4 ^ (n + 2) : by rw twice_m,
  },
  {
    cases lt_trichotomy 1 n.succ with one_lt_n n_lt_one,
    {
      have u : nat.succ n + 1 = n.succ.succ, norm_num,
      rw <- u,
      have recurse : n.succ < n.succ.succ, exact lt_add_one (nat.succ n),
      let e := product_primes_bound n.succ,
      rw <- extend_prime_product_odd (nat.succ (nat.succ n)) (by linarith) (increment_bit _ h),
      calc ∏ i in finset.filter nat.prime (finset.range (n + 2)), i
            ≤ 4 ^ n.succ : product_primes_bound n.succ
        ... ≤ 4 ^ (n + 2) : nat.le_add_left _ _,
    },
    cases n_lt_one,
    {
      cases n,
      exact le_of_inf_eq rfl,
      exfalso, exact add_one_zero n (eq.symm (nat.succ_inj n_lt_one)),
    },
    {
      have e : n < 0, exact nat.lt_of_succ_lt_succ n_lt_one,
      interval_cases n,
    }
  }
end
