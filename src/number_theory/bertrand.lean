/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/

import data.nat.prime
import data.finset.intervals
import data.nat.multiplicity
import data.nat.choose.sum
import data.padics.padic_norm
import tactic
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial

open_locale big_operators

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n : nat) (p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p (nat.choose (2 * n) n)

lemma central_binom_nonzero (n : ℕ) : nat.choose (2 * n) n ≠ 0 :=
ne_of_gt (nat.choose_pos (by linarith))

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  have bar : (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ nat.log p (2 * n),
    calc (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : by apply finset.card_filter_le
    ... = (nat.log p (2 * n) + 1) - 1 : by simp,
  have baz : p ^ (nat.log p (2 * n)) ≤ 2 * n,
  { apply nat.pow_log_le_self,
    apply hp.out.one_lt,
    calc 1 ≤ 3 : dec_trivial
    ...    ≤ n : n_big
    ...    ≤ 2 * n : by linarith, },
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) bar) baz,
end

lemma add_two_not_le_one (x : nat) (pr : x.succ.succ ≤ 1) : false :=
  nat.not_succ_le_zero x (nat.lt_succ_iff.mp pr)

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
begin
  have h1 : p ^ α n p < p ^ 2,
    calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
    ...            < p ^ 2 : smallish,

  let h2 := (pow_lt_pow_iff hp.out.one_lt).1 h1,
  omega,
  -- -- pow_lt_pow_iff
  -- unfold α,
  -- rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  -- simp only [@nat.prime.multiplicity_choose p (2 * n) n _ hp.out (by linarith) (le_refl (2 * n))],
  -- have r : 2 * n - n = n, by
  --   calc 2 * n - n = n + n - n: by rw two_mul n
  --   ... = n: nat.add_sub_cancel n n,
  -- simp only [r, finset.filter_congr_decidable],
  -- have s : ∀ i, p ^ i ≤ n % p ^ i + n % p ^ i → i ≤ 1, by
  --   { intros i pr,
  --     cases le_or_lt i 1, {exact h,},
  --     { exfalso,
  --       have u : 2 * n < 2 * (n % p ^ i), by
  --         calc 2 * n < p ^ 2 : smallish
  --         ... ≤ p ^ i : nat.pow_le_pow_of_le_right (nat.prime.pos is_prime) h
  --         ... ≤ n % p ^ i + n % p ^ i : pr
  --         ... = 2 * (n % p ^ i) : (two_mul _).symm,
  --       have v : n < n % p ^ i, by linarith,
  --       have w : n % p ^ i ≤ n, exact (nat.mod_le _ _),
  --       linarith, }, },
  -- have t : ∀ x ∈ finset.Ico 1 (2 * n), p ^ x ≤ n % p ^ x + n % p ^ x ↔ (x ≤ 1 ∧ p ^ x ≤ n % p ^ x + n % p ^ x), by
  --   {
  --     intros x size,
  --     split,
  --     { intros bound, split, exact s x bound, exact bound, },
  --     { intros size2,
  --       cases x,
  --       { simp at size, trivial, },
  --       { cases x,
  --         { exact size2.right, },
  --         { exfalso, exact nat.not_succ_le_zero _ (nat.lt_succ_iff.mp (size2.left)), }, }, },
  --   },
  -- simp only [finset.filter_congr t],
  -- simp only [finset.filter_and],
  -- simp only [@finset.Ico.filter_Ico_bot 1 (2 * n) (by linarith)],
  -- exact finset.card_singleton_inter,
end

lemma move_mul (m p i : nat) (b : m < i * p) : m / p < i :=
begin
  cases lt_or_le (m / p) i,
  { exact h },
  exfalso,
  let u : i * p ≤ m := le_trans (nat.mul_le_mul_right p h) (nat.div_mul_le_self m p),
  linarith,
end

private lemma collapse_enat (n : enat) (s : 2 = n + 1 + 1) : n = 0 :=
begin
  have u : 0 + 1 = n + 1, by simpa using (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 s,
  have v : 0 = n, by exact (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 u,
  exact v.symm
end

lemma twice_nat_small : ∀ (n : nat) (h : 2 * n < 2), n = 0
| 0 := λ _, rfl
| (n + 1) := λ pr, by linarith

lemma pow_big : ∀ (i p : nat) (p_pos : 0 < p) (i_big : 1 < i), p * p ≤ p ^ i
| 0 := λ _ _ pr, by linarith
| 1 := λ _ _ pr, by linarith
| (i + 2) := λ p p_pos i_big, by {
  calc p * p = p ^ 2 : by ring_exp
  ... ≤ p ^ (i + 2) : nat.pow_le_pow_of_le_right p_pos i_big,
}

lemma claim_3
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 6 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : α n p = 0
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp only [r, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear r,

  let p_pos : 0 < p := trans zero_lt_one hp.out.one_lt,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.Ico.mem at i_in_interval,
  have three_lt_p : 3 ≤ p ,
    { rcases le_or_lt 3 p with H|H,
      { exact H, },
      { have bad: 12 < 9, by
          calc 12 = 2 * 6: by ring
            ... <  2 * n: (mul_lt_mul_left (by linarith)).2 n_big
            ... < 3 * p: big
            ... < 3 * 3: (mul_lt_mul_left (by linarith)).2 H
            ... = 9: by ring,
        linarith, }, },

  simp only [not_le],

  rcases lt_trichotomy 1 i with H|rfl|H,
    { have two_le_i : 2 ≤ i, by linarith,
      have two_n_lt_pow_p_i : 2 * n < p ^ i,
        { calc 2 * n < 3 * p: big
            ... ≤ p * p: (mul_le_mul_right p_pos).2 three_lt_p
            ... = p ^ 2: by ring
            ... ≤ p ^ i: nat.pow_le_pow_of_le_right p_pos two_le_i, },
      have n_mod : n % p ^ i = n,
        { apply nat.mod_eq_of_lt,
          calc n ≤ n + n: nat.le.intro rfl
              ... = 2 * n: (two_mul n).symm
              ... < p ^ i: two_n_lt_pow_p_i, },
      rw n_mod,
      exact two_n_lt_pow_p_i, },

    { rw [pow_one],
      suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
      { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },

      have n_big : 1 ≤ (n / p),
        { apply (nat.le_div_iff_mul_le' p_pos).2,
          simp only [one_mul],
          exact small, },

      rw [←mul_add, nat.div_add_mod],
      let h5 : p * 1 ≤ p * (n / p) := nat.mul_le_mul_left p n_big,

      linarith, },
    { linarith, },
end


lemma claim_4
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (multiplicity_pos : α n p > 0)
  : p ≤ 2 * n
  :=
begin
  unfold α at multiplicity_pos,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n) at multiplicity_pos,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))] at multiplicity_pos,
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable] at multiplicity_pos,
  clear r,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp only [finset.Ico.mem, finset.mem_filter] at hm,
  calc p = p ^ 1 : tactic.ring_exp.base_to_exp_pf rfl
  ...    ≤ p ^ m : nat.pow_le_pow_of_le_right (by linarith [hp.out.one_lt]) hm.left.left
  ...    ≤ 2 * (n % p ^ m) : hm.right
  ...    ≤ 2 * n : nat.mul_le_mul_left _ (nat.mod_le n _),
end

/-
Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes <= 2n) p^(α n p) * (2n+1) ---- need to prove this
= prod (primes <= n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 3
= prod (primes <= 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 2
≤ prod (primes <= sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by primorial bound, proved in different PR
≤ prod (primes <= sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 1
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by "prime count of x is less than x", need to prove

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.
-/

lemma two_n_div_3_le_two_mul_n_choose_n (n : ℕ) : 2 * n / 3 < (2 * n).choose n :=
begin
  cases n,
  { simp only [nat.succ_pos', nat.choose_self, nat.zero_div, mul_zero], },
  calc 2 * (n + 1) / 3 < 2 * (n + 1): nat.div_lt_self (by norm_num) (by norm_num)
  ... = (2 * (n + 1)).choose(1): by norm_num
  ... ≤ (2 * (n + 1)).choose(2 * (n + 1) / 2): nat.choose_le_middle 1 (2 * (n + 1))
  ... = (2 * (n + 1)).choose(n + 1): by simp only [nat.succ_pos', nat.mul_div_right]
end

lemma not_pos_iff_zero (n : ℕ) : ¬ 0 < n ↔ n = 0 :=
begin
  split,
  { intros h, induction n, refl, simp only [nat.succ_pos', not_true] at h, cc, },
  { intros h, rw h, exact irrefl 0, },
end

lemma alskjhads (n x : ℕ): 2 * n / 3 + 1 ≤ x -> 2 * n < 3 * x :=
begin
  intro h,
  rw nat.add_one_le_iff at h,
  cases lt_or_ge (2 * n) (3 * x),
  { exact h_1, },
  { exfalso,
    simp only [ge_iff_le] at h_1,
    induction x,
    { simp at h, exact h, },
    { apply x_ih,
      cases lt_or_ge (2 * n / 3) x_n,
      { exact h_2, },
      { have r : 2 * n / 3 = x_n, by omega,
        exfalso,
        subst r,
        exact nat.lt_le_antisymm (nat.lt_mul_div_succ (2 * n) (by norm_num)) h_1, },
      { calc 3 * x_n ≤ 3 * (x_n + 1): by norm_num
        ... ≤ 2 * n: h_1, }, }, },
end

lemma central_binom_factorization (n : ℕ) :
      ∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      = (2 * n).choose n :=
  prod_pow_prime_padic_val_nat _ (central_binom_nonzero n) _ (lt_add_one _)

def central_binom_lower_bound := nat.four_pow_le_two_mul_add_one_mul_central_binom

lemma prod_of_pos_is_pos {S: finset ℕ} {f: ℕ → ℕ} (p_pos: ∀ p, p ∈ S → 0 < f p): 0 < ∏ p in S, f p :=
begin
  have prop : ∀ p, p ∈ S → f p ≠ 0, by
    { intros p p_in_s,
      specialize p_pos p p_in_s,
      linarith, },
  let e := finset.prod_ne_zero_iff.2 prop,
  cases lt_or_ge 0 (∏ p in S, f p),
  { exact h, },
  { exfalso,
    simp only [ge_iff_le, le_zero_iff] at h,
    exact e h, },
end

lemma interchange_filters {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f] [decidable_pred g] : (S.filter g).filter f = S.filter (λ i, g i ∧ f i) :=
begin
  ext1,
  simp only [finset.mem_filter],
  exact and_assoc (a ∈ S) (g a),
end

lemma interchange_and_in_filter {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f] [decidable_pred g] : S.filter (λ i, g i ∧ f i) = S.filter (λ i, f i ∧ g i) :=
begin
  ext1,
  simp only [finset.mem_filter, and.congr_right_iff],
  intros _,
  exact and.comm,
end

lemma intervening_sqrt {a n : ℕ} (small : (nat.sqrt n) ^ 2 ≤ a ^ 2) (big : a ^ 2 ≤ n) : a = nat.sqrt n :=
begin
  rcases lt_trichotomy a (nat.sqrt n) with H|rfl|H,
  { exfalso,
    have bad : a ^ 2 < a ^ 2, by
      calc a ^ 2 = a * a: by ring
      ... < (nat.sqrt n) * nat.sqrt n : nat.mul_self_lt_mul_self H
      ... = (nat.sqrt n) ^ 2: by ring
      ... ≤ a ^ 2 : small,
    exact nat.lt_asymm bad bad, },
  { refl, },
  { exfalso,
    have r: n < a ^ 2 :=
      calc n < a * a: nat.sqrt_lt.1 H
      ... = a ^ 2: by ring,
    linarith, },
end

lemma filter_filter_card_le_filter_card {α: _} {S: finset α} {f g: α → Prop} [_inst : decidable_pred f][_inst : decidable_pred g] : ((S.filter g).filter f).card ≤ (S.filter f).card :=
begin
  calc ((S.filter g).filter f).card = (S.filter (λ i, g i ∧ f i)).card: congr_arg finset.card interchange_filters
  ... = (S.filter (λ i, f i ∧ g i)).card: congr_arg finset.card interchange_and_in_filter
  ... = ((S.filter f).filter g).card: congr_arg finset.card interchange_filters.symm
  ... ≤ (S.filter f).card: (finset.filter f S).card_filter_le g,
end

lemma filter_size {S : finset ℕ} {a : ℕ} : (finset.filter (λ p, p < a) S).card ≤ a :=
begin
  have t : ∀ i, i ∈ (S.filter (λ p, p < a)) → i ∈ finset.range(a),
    { intros i hyp,
      simp only [finset.mem_filter] at hyp,
      simp only [finset.mem_range],
      exact hyp.2, },
  have r: S.filter (λ p, p < a) ⊆ finset.range(a) := finset.subset_iff.mpr t,
  have s: (S.filter (λ p, p < a)).card ≤ (finset.range(a)).card := finset.card_le_of_subset r,
  simp only [finset.card_range] at s,
  exact s,
end

lemma even_prime_is_two {p : ℕ} (pr: nat.prime p) (div: 2 ∣ p) : p = 2 :=
begin
  rcases pr with ⟨_, divs⟩,
  specialize divs 2 div,
  cc,
end

lemma even_prime_is_small {a n : ℕ} (a_prime : nat.prime a) (n_big : 2 < n) (small : a ^ 2 ≤ 2 * n): a ^ 2 < 2 * n :=
begin
  cases lt_or_ge (a ^ 2) (2 * n),
  { exact h, },
  { have t : a * a = 2 * n, by
      calc a * a = a ^ 2: by ring
      ... = 2 * n: by linarith,

    have two_prime : nat.prime 2, by norm_num,
    have a_even : 2 ∣ a := (or_self _).mp ((nat.prime.dvd_mul two_prime).mp ⟨n, t⟩),
    have a_two : a = 2 := even_prime_is_two a_prime a_even,
    subst a_two,
    linarith, },
end

lemma pow_sub_lt (a b c d : ℕ) (b_ge_d : b ≥ d) : a ^ b < c * a ^ d -> a ^ (b-d) < c :=
begin
  intro h,
  sorry,
end

lemma le_iff_mul_le_mul (a b c : ℕ) (c_pos : 0 < c) : a ≤ b ↔ a * c ≤ b * c :=
begin
  exact (mul_le_mul_right c_pos).symm
end

lemma three_pos : 0 < 3 := by dec_trivial

lemma ge_of_le (a b : ℕ) : a ≤ b → b ≥ a := ge.le

-- lemma false_inequality_is_false_alternate {n : ℕ} (n_large : 999 < n) : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) → false :=
-- begin
--   intro h,
--   have h1 : 4 ^ (n - (2 * n / 3 + 1)) < (2 * n + 1) * (2 * n) ^ nat.sqrt (2 * n),
--     apply pow_sub_lt,
--   -- apply ge_of_le,

--   apply (mul_le_mul_right three_pos).1,
--   -- rw add_mul,
--   -- simp only [one_mul],
--   -- linarith,
--   linarith [nat.div_mul_le_self (2 * n) 3],
--   exact h,


-- end

-- lemma le_of_pow_le_pow (a b c : nat) (c_pos : 0 < c) : a ^ c ≤ b ^ c → a ≤ b :=
-- begin
--   -- library_search,
--   sorry,
-- end

lemma power_conversion_1 (n : ℕ) (n_large : 999 < n) : 2 * n + 1 ≤ 4 ^ (n / 15) :=
begin
  suffices h : (2 * n + 1) ^ 15 ≤ (4 ^ (n / 15)) ^ 15,
    apply le_of_pow_le_pow 15,
    apply zero_le,
    linarith,
    exact h,

  induction n,
  simp,
  by_cases h : 999 < n_n,
  have odafij := n_ih h,
  rw nat.mul_succ,
  sorry,
  sorry,

end


lemma power_conversion_2 (n : ℕ) (n_large : 999 < n) : (2 * n) ^ nat.sqrt (2 * n) ≤ 4 ^ (n / 4) :=
begin
  sorry,
end


lemma false_inequality_is_false {n : ℕ} (n_large : 999 < n) : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) → false :=
begin
  rw imp_false,
  rw not_lt,
  calc (2 * n + 1) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1)
       ≤ (4 ^ (n / 15)) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_right ((2 * n) ^ nat.sqrt (2 * n))),
            apply power_conversion_1,
            finish
          end
  ...  ≤ (4 ^ (n / 15)) * (4 ^ (n / 4)) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_left (4 ^ (n / 15))),
            apply power_conversion_2,
            finish
          end
  ...  ≤ 4 ^ n :
          begin
            rw tactic.ring.pow_add_rev,
            rw tactic.ring.pow_add_rev,
            apply nat.pow_le_pow_of_le_right,
            dec_trivial,
            sorry,
          end
end

lemma blah {a : _} {A : finset a} {B : finset a} (p : A ⊆ B) : A.card ≤ B.card :=
begin
  exact finset.card_le_of_subset p
end

lemma more_restrictive_filter_means_smaller_subset {a : _} {S : finset a} {f : _} {g : _} [decidable_pred f] [decidable_pred g] (p : ∀ i, f i → g i): finset.filter f S ⊆ finset.filter g S :=
begin
  intros h prop,
  simp only [finset.mem_filter] at prop,
  simp only [finset.mem_filter],
  exact ⟨prop.1, p h prop.2⟩,
end

lemma filter_to_subset {a : _} {S : finset a} {T : finset a} {p : _} [decidable_pred p] (prop : ∀ i, p i → i ∈ T)
  : finset.filter p S ⊆ T :=
begin
  suffices : ∀ x, x ∈ finset.filter p S → x ∈ T, by exact finset.subset_iff.mpr this,
  intros x hyp,
  simp only [finset.mem_filter] at hyp,
  exact prop x hyp.2
end

lemma foo {n : ℕ} : (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card ≤ nat.sqrt (2 * n) :=
begin
  have t : ∀ p, p ^ 2 ≤ 2 * n ↔ p ≤ nat.sqrt (2 * n),
  { intro p,
    have r : p ^ 2 = p * p, by ring,
    rw r,
    exact nat.le_sqrt.symm, },

  have u : ∀ p, (p ^ 2 < 2 * n) → p ^ 2 ≤ 2 * n, by
  { intros p hyp,
    exact le_of_lt hyp, },

  have v : finset.filter (λ p, p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) ⊆
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) :=
    more_restrictive_filter_means_smaller_subset u,

  have w' : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) :=
    by {
      apply congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime i)),
      exact finset.range_eq_Ico (2 * n / 3 + 1),
    },

  have w : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { refine congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) i) _,
      ext1,
      split,
      { intros hyp,
        simp only [true_and, finset.Ico.mem, zero_le', finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        exact ⟨⟨nat.prime.two_le hyp.2, hyp.1⟩, hyp.2⟩, },
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [true_and, finset.Ico.mem, zero_le', finset.mem_filter],
        exact ⟨hyp.1.2, hyp.2⟩, }, },

  have g : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))) =
    finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { ext1,
      split,
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        have r : 2 ≤ a ^ 2 :=
          by calc 2 ≤ a : nat.prime.two_le hyp.1.2
          ... ≤ a * a : nat.le_mul_self a
          ... = a ^ 2 : by ring,
        exact ⟨hyp.1, ⟨r, hyp.2⟩⟩, },
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        exact ⟨hyp.1, hyp.2.2⟩, }, },

  have h : (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))) ⊆ finset.Ico 2 (nat.sqrt (2 * n) + 1)
    , by {
      apply filter_to_subset _,
      intros i hyp,
      simp,
      split,
      { cases le_or_gt 2 i,
        { exact h, },
        { cases i,
          { linarith, },
          { cases i,
            { linarith, },
            { exact dec_trivial, }, } }, },
      { have s : i * i ≤ 2 * n,
          calc i * i = i ^ 2 : by ring
          ... ≤ 2 * n : hyp.2,
        have r : i ≤ nat.sqrt (2 * n) := nat.le_sqrt.mpr s,
        linarith, },
    },

  calc (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card
      ≤ (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card: finset.card_le_of_subset v
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1)))).card: congr_arg finset.card w'
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card w
  ... = (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card g
  ... ≤ (finset.Ico 2 (nat.sqrt (2 * n) + 1)).card: finset.card_le_of_subset h
  ... = nat.sqrt (2 * n) + 1 - 2: finset.Ico.card 2 (nat.sqrt (2 * n) + 1)
  ... = nat.sqrt (2 * n) - 1: by ring
  ... ≤ nat.sqrt (2 * n): (nat.sqrt (2 * n)).sub_le 1,

end

lemma bertrand_eventually (n : nat) (n_big : 1000 ≤ n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  by_contradiction no_prime,

  have central_binom_factorization_small :
      ∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      =
      ∏ p in finset.filter nat.prime (finset.range (((2 * n).choose n + 1))),
        p ^ (padic_val_nat p ((2 * n).choose n)) ,
    { apply finset.prod_subset,
      apply finset.subset_iff.2,
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intro hx,
      split,
      { linarith [(hx.left), (two_n_div_3_le_two_mul_n_choose_n n)], },
      { exact hx.right, },
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intros hx h2x,
      simp only [hx.right, and_true, not_lt] at h2x,
      by_contradiction,
      have x_le_two_mul_n : x ≤ 2 * n, by
        { apply (@claim_4 x ⟨hx.right⟩ n),
          unfold α,
          simp only [gt_iff_lt],
          by_contradiction h1,
          rw not_pos_iff_zero at h1,
          rw h1 at h,
          rw pow_zero at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
      apply no_prime,
      use x,
      split,
      { exact hx.right, },
      { split,
        { by_contradiction neg_n_le_x,
          simp only [not_lt] at neg_n_le_x,
          have claim := @claim_3 x ⟨hx.right⟩ n (by linarith) (by linarith) (alskjhads n x h2x),
          unfold α at claim,
          rw [claim, pow_zero] at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
        exact x_le_two_mul_n, }, },

    have double_pow_pos: ∀ (i : ℕ), 0 < (2 * n) ^ i,
    { intros _, exact pow_pos (by linarith) _ },

    have binom_inequality : (2 * n).choose n < (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1), by
      calc (2 * n).choose n
              = (∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : (central_binom_factorization n).symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : central_binom_factorization_small.symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   if p ^ 2 ≤ 2 * n then p ^ (padic_val_nat p ((2 * n).choose n)) else p ^ (padic_val_nat p ((2 * n).choose n)))
                       : by simp only [if_t_t]
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, ¬p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                    : finset.prod_ite _ _
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : by simp only [not_le, finset.filter_congr_decidable]
      ...     ≤ (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   2 * n)
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine finset.prod_le_prod'' _,
                       intros i hyp,
                       simp only [finset.mem_filter, finset.mem_range] at hyp,
                       exact @claim_1 i (fact_iff.2 hyp.1.2) n (by linarith),
                     end
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 ≤ 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : by simp only [finset.prod_const]
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 < 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : begin
                    refine (nat.mul_left_inj _).2 _,
                    { refine prod_of_pos_is_pos _,
                      intros p hyp,
                      simp only [finset.mem_filter, finset.mem_range] at hyp,
                      exact pow_pos (nat.prime.pos hyp.1.2) (padic_val_nat p ((2 * n).choose n)), },
                    { refine congr_arg (λ i, (2 * n) ^ i) _,
                      refine congr_arg (λ s, finset.card s) _,
                      ext1,
                      split,
                      { intro h, simp at h, simp, split, exact h.1, exact even_prime_is_small h.1.2 (by linarith) h.2, },
                      { intro h, simp at h, simp, split, exact h.1, linarith, }
                     },
                   end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine pow_le_pow (by linarith) _,
                       exact foo,
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                        { refine finset.prod_le_prod'' _,
                          intros i hyp,
                          simp only [finset.mem_filter, finset.mem_range] at hyp,
                          cases hyp with i_facts sqrt_two_n_lt_i,
                          refine pow_le_pow _ _,
                          { cases le_or_gt 1 i,
                            { exact h, },
                            { have i_zero : i = 0, by linarith,
                              rw i_zero at i_facts,
                              exfalso,
                              exact nat.not_prime_zero i_facts.2, }, },
                          { exact @claim_2 i (fact_iff.2 i_facts.2) n (by linarith) sqrt_two_n_lt_i, }, },
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                       refine finset.prod_le_prod_of_subset_of_one_le' (finset.filter_subset _ _) _,
                        { intros i hyp1 hyp2,
                        cases le_or_gt 1 i,
                        { ring_nf, exact h, },
                        { have i_zero : i = 0, by linarith,
                          simp only [i_zero, true_and, nat.succ_pos', finset.mem_filter, finset.mem_range] at hyp1,
                          exfalso, exact nat.not_prime_zero hyp1, }, }
                     end
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p)
                     : by simp only [pow_one]
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
               *
                (primorial (2 * n / 3))
                     : by unfold primorial
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3)
                     : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3))
      ...     < (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3 + 1)
                : (mul_lt_mul_left (pow_pos (by linarith) _)).mpr (pow_lt_pow (by simp only [nat.succ_pos', nat.one_lt_bit0_iff, nat.one_le_bit0_iff]) (by simp only [nat.succ_pos', lt_add_iff_pos_right])),

    have false_inequality : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1), by
      calc 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n : central_binom_lower_bound n
        ...      < (2 * n + 1) * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1))
                    : nat.mul_lt_mul_of_pos_left binom_inequality (by linarith)
        ...      = (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) : by ring,

    exfalso,
    exact false_inequality_is_false (by linarith) false_inequality,
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
cases le_or_lt 1000 n,
{exact bertrand_eventually n h},

cases le_or_lt 505 n,
{ use 1009, norm_num, split, linarith, linarith, },
clear h,

cases le_or_lt 376 n,
{ use 751, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 274 n,
{ use 547, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 139 n,
{ use 277, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 70 n,
{ use 139, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 37 n,
{ use 73, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 19 n,
{ use 37, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 11 n,
{ use 19, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 6 n,
{ use 11, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 4 n,
{ use 7, norm_num, split, linarith, linarith, },
clear h,
interval_cases n,
{ use 2, norm_num },
{ use 3, norm_num },
{ use 5, norm_num },
end
