/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/

import data.nat.prime
import data.finset.intervals
import data.nat.multiplicity
import data.nat.choose.sum
import number_theory.padics.padic_norm
import tactic
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial
import analysis.special_functions.pow
import analysis.special_functions.sqrt
import analysis.calculus.local_extr
import data.real.sqrt
import data.real.nnreal

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
  have prime_powers_sparse :
    (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card
    ≤ nat.log p (2 * n),
    calc
      (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card
        ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : by apply finset.card_filter_le
    ... = (nat.log p (2 * n) + 1) - 1 : by simp,
  have p_pow_small : p ^ (nat.log p (2 * n)) ≤ 2 * n,
  { apply nat.pow_log_le_self,
    apply hp.out.one_lt,
    calc 1 ≤ 3 : dec_trivial
    ...    ≤ n : n_big
    ...    ≤ 2 * n : by linarith, },
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) prime_powers_sparse) p_pow_small,
end

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

  let h2 : α n p < 2 := (pow_lt_pow_iff hp.out.one_lt).1 h1,
  linarith,
end

lemma twice_nat_small : ∀ (n : nat) (h : 2 * n < 2), n = 0
| 0 := λ _, rfl
| (n + 1) := λ pr, by linarith

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
                        hp.out (by linarith) (lt_add_one (nat.log p (2 * n)))] at multiplicity_pos,
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable]
    at multiplicity_pos,
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
= prod (primes ≤ 2n) p^(α n p) * (2n+1)
= prod (primes ≤ n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 3)
= prod (primes ≤ 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p^α
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 2)
≤ prod (primes ≤ sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by a general bound on the primorial)
≤ prod (primes ≤ sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 1)
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by "prime count of x is less than x")

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
    have: n < a ^ 2 :=
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

lemma pow_beats_mul (n : ℕ) (big : 3 < n) : 32 * n ≤ 4 ^ n :=
begin
  induction n with n hyp,
  { linarith, },
  { cases le_or_gt n 3,
    { have r : 2 < n := nat.succ_lt_succ_iff.mp big,
      have s : n = 3 := by linarith,
      rw s,
      norm_num, },
    { specialize hyp h,
      have s : 0 < 4 ^ n := pow_pos (by norm_num) _,
      have r : 32 ≤ 4 ^ n := by linarith,
      calc 32 * (n + 1) = 32 * n + 32 : by ring
      ... ≤ 4 ^ n + 32 : by linarith
      ... ≤ 4 ^ n + 4 ^ n : by linarith
      ... = (4 ^ n) * 2 : by ring
      ... ≤ (4 ^ n) * 4 : by linarith
      ... ≤ 4 ^ (n + 1) : by ring_exp, }, },
end

lemma power_conversion_1 (n : ℕ) (n_large : 480 < n) : 2 * n + 1 ≤ 4 ^ (n / 15) :=
begin
  have : 31 ≤ n / 15,
    { cases le_or_gt 31 (n / 15),
      { exact h, },
      { have r : n < n :=
          calc n = 15 * (n / 15) + (n % 15) : (nat.div_add_mod n 15).symm
            ... < 15 * 31 + (n % 15) : add_lt_add_right ((mul_lt_mul_left (nat.succ_pos 14)).2 h) _
            ... < 15 * 31 + 15 : add_lt_add_left (nat.mod_lt n (by linarith)) (15 * 31)
            ... = 480 : by norm_num
            ... < n : n_large,
        exfalso,
        exact lt_irrefl _ r, }, },
  have rem_small : (n % 15) < 15 := nat.mod_lt n (nat.succ_pos 14),
  calc 2 * n + 1 = 2 * (15 * (n / 15) + (n % 15)) + 1 : by rw nat.div_add_mod n 15
  ... = 30 * (n / 15) + 2 * (n % 15) + 1 : by ring
  ... ≤ 30 * (n / 15) + 2 * 15 + 1 : by linarith
  ... = 30 * (n / 15) + 31 : by norm_num
  ... ≤ 31 * (n / 15) + 31 : by linarith
  ... ≤ 31 * (n / 15) + (n / 15) : by linarith
  ... = 32 * (n / 15) : by ring
  ... ≤ 4 ^ (n / 15) : pow_beats_mul (n / 15) (by linarith),
end

open real
open_locale nnreal

lemma pow_coe (a b : ℕ) : (↑(a ^ b) : ℝ) = (↑a) ^ (↑b : ℝ) :=
begin
  rw real.rpow_nat_cast,
  simp only [nat.cast_pow],
end

lemma nat_sqrt_le_real_sqrt (a : ℕ) : (nat.sqrt a : ℝ) ≤ real.sqrt a :=
begin
  have sqrt_pos : (0 : ℝ) ≤ ((nat.sqrt a) : ℝ) :=
    (@nat.cast_le ℝ _ _ 0 (nat.sqrt a)).2 (zero_le (nat.sqrt a)),

  apply (le_sqrt (nat.sqrt a).cast_nonneg (nat.cast_nonneg a)).2,
  calc ↑(nat.sqrt a) ^ 2 = (nat.sqrt a : ℝ) ^ (1 + 1) : rfl
  ... = (nat.sqrt a : ℝ) ^ ↑(1 + 1) : (rpow_nat_cast (nat.sqrt a : ℝ) (1 + 1)).symm
  ... = (nat.sqrt a : ℝ) ^ ((1 : ℝ) + 1) : by simp only [nat.cast_add, nat.cast_one]
  ... = ((nat.sqrt a) : ℝ) ^ (1 : ℝ) * ((nat.sqrt a) : ℝ) ^ (1 : ℝ) :
        by rw rpow_add' sqrt_pos two_ne_zero
  ... = ↑(nat.sqrt a) * ↑(nat.sqrt a) : by rw rpow_one
  ... = ↑(nat.sqrt a * nat.sqrt a) : by norm_num
  ... ≤ ↑a : nat.cast_le.mpr (nat.sqrt_le a),
end

open set

noncomputable def fff (x : ℝ) := x * log 4 - sqrt (8 * x + 8) * log (8 * x + 8)

noncomputable def fff' (x : ℝ) := log 4 - (((8 / (2 * (sqrt (8 * x + 8)))) * log (8 * x + 8)) + (sqrt (8 * x + 8) * (8 / (8 * x + 8))))

lemma derivative_fff {x : ℝ} (h : 0 < x) : has_deriv_at (λ x, fff x) (fff' x) x :=
begin
  have linear_deriv: has_deriv_at (λ (x : ℝ), 8 * x + 8) 8 x,
    { refine has_deriv_at.add_const _ _,
      simpa using has_deriv_at.const_mul (8 : ℝ) (has_deriv_at_id x), },
  unfold fff,
  refine has_deriv_at.sub _ _,
  { suffices: has_deriv_at (λ x, x * log 4) (1 * log 4) x, by simpa using this,
    refine has_deriv_at.mul_const _ _,
    exact has_deriv_at_id _, },
  { refine @has_deriv_at.mul _ _ x (λ x, sqrt (8 * x + 8)) (λ x, log (8 * x + 8)) _ _ _ _,
    { refine has_deriv_at.sqrt _ _,
      { exact linear_deriv, },
      { linarith, }, },
    { refine has_deriv_at.log _ _,
      { exact linear_deriv, },
      { linarith, }, }, },
end

lemma fff'_is_deriv {x : ℝ} (h : 0 < x) : deriv fff x = fff' x :=
by refine has_deriv_at.deriv (derivative_fff h)

lemma foobar {x : ℝ} (h : 0 < x) : sqrt x * (1 / x) = 1 / sqrt x :=
begin
  have g : x = sqrt x * sqrt x, by rw mul_self_sqrt (le_of_lt h),
  calc sqrt x * (1 / x) = 1 * (sqrt x / x) : mul_div_comm _ _ _
  ... = (sqrt x / x) : one_mul _
  ... = sqrt x / (sqrt x * sqrt x) : by rw <- g
  ... = 1 / sqrt x : div_mul_right _ (ne_of_gt (sqrt_pos.2 h)),
end

lemma foobar' {x : ℝ} (h : 0 < x) : sqrt x / x = 1 / sqrt x :=
begin
  calc sqrt x / x = sqrt x * (1 / x) : by ring
  ... = 1 / sqrt x : foobar h
end

private noncomputable def aux (x : ℝ) :=
  sqrt 2 * sqrt (x + 1) * log 2 - (log (8 * (x + 1)) + 2)

private noncomputable def aux' (x : ℝ) :=
  sqrt 2 * (1 / (2 * sqrt (x + 1))) * log 2 - 8 / (8 * (x + 1))

lemma derivative_aux {x : ℝ} (hyp : x ≠ -1) : has_deriv_at (λ x, aux x) (aux' x) x :=
begin
  unfold aux,
  refine has_deriv_at.sub _ _,
  { refine has_deriv_at.mul_const _ _,
    refine has_deriv_at.const_mul _ _,
    refine has_deriv_at.sqrt _ _,
    { refine has_deriv_at.add_const _ _,
      exact has_deriv_at_id x, },
    { intro bad,
      have t : x = -1, by linarith,
      exact hyp t, }, },
  { refine has_deriv_at.add_const _ _,
    refine has_deriv_at.log _ _,
    { ring_nf,
      refine has_deriv_at.add_const _ _,
      simpa using has_deriv_at.const_mul 8 (has_deriv_at_id x), },
    { intros bad,
      have t : x = -1, by linarith,
      exact hyp t, }, },
end

lemma sqrt_log_bound : 0 < sqrt 2 * log 2 / 2 :=
begin
  refine div_pos _ (by norm_num),
    { refine mul_pos _ _,
      { exact sqrt_pos.2 (by norm_num), },
      { exact log_pos (by norm_num), },
    },
end

lemma aux_bound : 1 / (sqrt 2 * log 2 / 2) ^ 2 - 1 ≤ (4 : ℝ) :=
begin
  suffices : 1 / (sqrt 2 * log 2 / 2) ^ 2 ≤ 5, by linarith,
  suffices : 1 ≤ (sqrt 2 * log 2 / 2) ^ 2 * 5,
    { have pos : 0 < (sqrt 2 * log 2 / 2) ^ 2,
      { refine sq_pos_of_ne_zero _ _,
        linarith [sqrt_log_bound], },
      rw div_le_iff' pos,
      exact this, },
  suffices : 1 ≤ (sqrt 2 * (log 2 / 2)) ^ 2 * 5,
    { rw mul_div_assoc, exact this, },
  suffices : 1 ≤ (sqrt 2) ^ 2 * (log 2 / 2) ^ 2 * 5,
    { rw mul_pow, exact this, },
  suffices : 1 ≤ 2 * (log 2 / 2) ^ 2 * 5,
    { rw sq_sqrt, exact this, norm_num, },
  suffices : 1 ≤ 5 / 2 * (log 2) ^ 2,
    { ring_nf, exact this, },
  suffices : 2 / 5 ≤ (log 2) ^ 2,
    { sorry, },
  sorry,
end

lemma aux_derivative_ge_zero (x : ℝ) (x_big : 4 ≤ x) : 0 ≤ aux' x :=
begin
  unfold aux',

  -- Multiply through by (x + 1)
  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) / 2 * log 2 - 1,
    { have h : 0 / (x + 1) ≤ (sqrt 2 * sqrt (x + 1) / 2 * log 2 - 1) / (x + 1),
      { have t : 0 < x + 1, by linarith,
        rw (div_le_div_iff t t),
        simpa using mul_nonneg this (le_of_lt t), },
      rw [zero_div, sub_div] at h,
      have eight_not_zero : (8 : ℝ) ≠ 0 := by norm_num,
      rw (div_mul_right _ eight_not_zero),
      rw mul_div_right_comm at h,
      rw [div_div_eq_div_mul, mul_comm 2 (x + 1), ←div_div_eq_div_mul, mul_div_assoc] at h,
      rw @foobar' (x + 1) (by linarith) at h,
      rw [mul_div_assoc, div_div_eq_div_mul, mul_comm (sqrt (x + 1)) 2] at h,
      exact h, },

  suffices: 1 ≤ sqrt 2 * log 2 / 2 * sqrt (x + 1), by linarith,

  suffices: 1 / (sqrt 2 * log 2 / 2) ≤ sqrt (x + 1),
    { refine (div_le_iff' _).mp this,
      exact sqrt_log_bound, },

  suffices: (1 / (sqrt 2 * log 2 / 2)) ^ 2 ≤ x + 1,
    { refine (le_sqrt _ (by linarith)).2 this,
      exact one_div_nonneg.2 (le_of_lt sqrt_log_bound), },

  suffices: (1 / (sqrt 2 * log 2 / 2)) ^ 2 - 1 ≤ x, by linarith,

  calc (1 / (sqrt 2 * log 2 / 2)) ^ 2 - 1
      = 1 / (sqrt 2 * log 2 / 2) ^ 2 - 1 : sorry
  ... ≤ (4 : ℝ) : aux_bound
  ... ≤ x : x_big,
end

lemma aux_zero : 0 ≤ aux 72 :=
begin
  unfold aux,
  norm_num,
  sorry,
end

lemma aux_pos (x : ℝ) (x_big : 72 ≤ x) : 0 ≤ aux x :=
begin
  sorry,
end

lemma deriv_nonneg {x : ℝ} (x_big : 72 ≤ x) : 0 ≤ fff' x :=
begin
  unfold fff',
  have r : 8 * x + 8 = 8 * (x + 1), by ring,
  rw r,
  simp only [zero_le_one, sqrt_mul, zero_le_bit0],
  have eight_not_zero : (8 : ℝ) ≠ 0 := by norm_num,
  have frac_simp: 8 / (8 * (x + 1)) = 1 / (x + 1), by rw div_mul_right _ eight_not_zero,
  rw frac_simp,
  rw mul_assoc (sqrt 8) (sqrt (x + 1)) (1 / (x + 1)),
  have g : sqrt 8 = 2 * sqrt 2,
    { have g : sqrt 8 = sqrt ((2 * 2) * 2), by norm_num,
      rw g,
      simp, },
  have eight_simp : 8 / (2 * (sqrt 8 * sqrt (x + 1))) = (2 / sqrt 2) * (1 / sqrt (x + 1)),
    { rw <- mul_assoc 2 (sqrt 8) (sqrt (x + 1)),
      rw div_mul_eq_div_mul_one_div,
      suffices : 8 / (2 * sqrt 8) = 2 / sqrt 2, by rw this,
      rw g,
      rw div_mul_eq_div_mul_one_div,
      norm_num,
      rw div_mul_eq_div_mul_one_div,
      rw <- mul_assoc,
      norm_num,
      rw mul_div_comm,
      norm_num, },

  rw eight_simp, clear eight_simp,
  rw g,
  rw @foobar (x + 1) (by linarith),

  -- Multiply through by sqrt (x + 1)
  suffices: 0 ≤ sqrt (x + 1) * log 4 - (2 / sqrt 2 * log (8 * (x + 1)) + 2 * sqrt 2),
    { sorry, },

  -- Multiply through by sqrt 2
  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * log 4 - (2 * log (8 * (x + 1)) + 4),
    { sorry, },

  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * (2 * log 2) - 2 * (log (8 * (x + 1)) + 2),
    { sorry, },

  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * log 2 - (log (8 * (x + 1)) + 2),
    { sorry, },

  -- Then easy to show it's positive, by taking the derivative.
  exact aux_pos x x_big,
end

lemma fff_differentiable {i : ℝ} (pr : 0 < i) : differentiable_on ℝ fff (interior (Ici i)) :=
begin
  have d : differentiable_on ℝ (λ (x : ℝ), 8 * x + 8) (interior (Ici i)),
    { refine differentiable_on.add_const _ _,
      refine differentiable_on.const_mul _ _,
      refine differentiable_on_id, },
  refine differentiable_on.sub _ _,
  { refine differentiable_on.mul_const _ _,
    refine differentiable_on_id, },
  { refine differentiable_on.mul _ _,
    { refine differentiable_on.comp _ _ _,
      { exact Ici i, },
      { refine differentiable_on.sqrt _ _,
        { refine differentiable_on_id, },
        { intros x,
          simp only [mem_Ici, ne.def],
          intros x_in,
          linarith, }, },
      { exact d, },
      { intro x,
        simp only [interior_Ici, mem_Ici, mem_Ioi, mem_preimage],
        intros x_big,
        calc i ≤ x : le_of_lt x_big
        ... ≤ 8 * x + 8 : by linarith,
      }, },
    { refine differentiable_on.log _ _,
      { exact d, },
      { intros x,
        simp only [interior_Ici, mem_Ioi, ne.def],
        intros x_big,
        linarith, }, }, },
end

lemma fff_continuous {i : ℝ} (pr : 0 < i) : continuous_on fff (Ici (i : ℝ)) :=
begin
  have e := differentiable_on.continuous_on (@fff_differentiable (i / 2) (by linarith)),
  have s : Ici i ⊆ interior (Ici (i / 2)),
    { simp only [interior_Ici],
      intro a,
      simp,
      intro a_in,
      linarith, },
  exact continuous_on.mono e s,
end

lemma fff_one : fff 1 < 0 :=
begin
  unfold fff,
  norm_num,
  calc log 4 < log 16 : log_lt_log (by linarith) (by linarith)
  ... = log 16 + 0 : by ring
  ... ≤ log 16 + (3 * log 16) :
    add_le_add_left (mul_nonneg (by linarith) ((log_nonneg_iff (by linarith)).2 (by linarith))) _
  ... = 4 * log 16 : by ring
  ... = sqrt (4 * 4) * log 16 : congr_arg (λ i, i * log 16) (by rw @sqrt_mul_self 4 (by linarith))
  ... = sqrt 16 * log 16 : by norm_num,
end

lemma sqrt_four : sqrt 4 = 2 :=
begin
  calc sqrt 4 = sqrt (2 * 2) : by norm_num
  ... = 2 : sqrt_mul_self (by linarith)
end

lemma log_pos_eq_zero {x : ℝ} (h : 0 < x) (hyp : log x = 0) : x = 1 :=
begin
  let e := log_inj_on_pos,
  have r : log 1 = 0 := log_one,
  have t : log x = log 1,
    { rw log_one,
      exact hyp, },
  have x_one := log_inj_on_pos,
  unfold inj_on at x_one,
  have x_pos : x ∈ Ioi (0 : ℝ) := by simpa using h,
  have one_pos : (1 : ℝ) ∈ Ioi (0 : ℝ) := by simp,
  specialize x_one x_pos one_pos t,
  exact x_one,
end

lemma log_eq_zero {x : ℝ} (hyp : log x = 0) : x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  cases lt_trichotomy x 0,
  { let e := log_abs x,
    rw (abs_of_neg h) at e,
    have t : 0 < -x := neg_pos.mpr h,
    have minus_x_is_one : -x = 1 := log_pos_eq_zero t (by linarith),
    exact or.inr (or.inr (eq_neg_of_eq_neg (eq.symm minus_x_is_one)))
  },
  { cases h,
    { exact or.inl h, },
    { exact or.inr (or.inl (log_pos_eq_zero h hyp)), }, },
end

lemma zero_pow_complex {a : ℂ} {x : ℂ} (hyp : 0 ^ x = a) : a = 0 ∨ (x = 0 ∧ a = 1) :=
begin
  unfold pow at hyp,
  unfold complex.cpow at hyp,
  simp at hyp,
  by_cases x = 0,
  { right,
    subst h,
    simp at hyp,
    cc, },
  { left,
    cc, },
end

lemma zero_pow_real {a : ℝ} {x : ℝ} (hyp : 0 ^ x = a) : a = 0 ∨ (x = 0 ∧ a = 1) :=
begin
  unfold pow at hyp,
  unfold rpow at hyp,
  simp at hyp,
  cases @zero_pow_complex _ x rfl with k_zero k_one,
  { left,
    simp [k_zero] at hyp,
    exact hyp.symm, },
  { cases k_one with x_zero a_one,
    simp [a_one] at hyp,
    right,
    exact ⟨complex.of_real_eq_zero.1 x_zero, hyp.symm⟩, },
end

lemma log_pow {x y : ℝ} : (x ≠ 0 ∨ y = 0) ↔ log (x ^ y) = y * log x :=
begin
  split,
  { intros hyp,
    have r : x ^ y = exp (log x * y),
    { unfold pow, unfold rpow, unfold pow, unfold complex.cpow,
      by_cases x = 0,
      { subst h,
        simp at hyp,
        subst hyp,
        simp, },
      { unfold exp, unfold log,
        have r : ¬ ((x : ℂ) = 0),
          { rename h x_nonzero,
            by_contradiction,
            apply x_nonzero,
            simp at h,
            exact h, },
        rw if_neg r,
        rw dif_neg h,
        unfold complex.log,
        sorry,
      },
    },
    rw [r, log_exp],
    exact mul_comm _ _,
  },
  { intros hyp,
    by_cases x = 0,
    { subst h,
      simp at hyp,
      cases log_eq_zero hyp,
      { sorry, },
      { cases h,
        { cases zero_pow_real h,
          { norm_num at h_1, },
          { right, exact h_1.1 }, },
        { cases zero_pow_real h,
          { norm_num at h_1, },
          { cases h_1 with _ bad,
            norm_num at bad, }, }, }, },
    { exact or.inl h, },
  },
end

lemma fff_250 : fff 250 > 0 :=
begin
  unfold fff,
  norm_num,
  have r : 11 * sqrt 502 < 250,
    { have s : (11 * sqrt 502) ^ 2 < 250 ^ 2,
      { calc (11 * sqrt 502) ^ 2 = 11 ^ 2 * (sqrt 502) ^ 2 : by rw mul_pow
        ... = 121 * (sqrt 502) ^ 2 : by norm_num
        ... = 121 * ((sqrt 502) * (sqrt 502)) : by sorry
        ... = 121 * 502 : by rw @mul_self_sqrt 502 (by norm_num)
        ... = 60742 : by norm_num
        ... < 250 ^ 2 : by norm_num, },
      have e := abs_lt_of_sq_lt_sq s (by norm_num),
      have u : 0 < 11 * sqrt 502, by norm_num,
      have v : abs (11 * sqrt 502) = 11 * sqrt 502 := abs_of_pos u,
      rw abs_of_pos u at e,
      exact e, },

  have eight_pow : (8 : ℝ) = 2 ^ 3 := by norm_num,
  have two_fifty_six_pow : (256 : ℝ) = 2 ^ 8 := by norm_num,

  have r : log 251 ≤ log 256 := (@log_le_log 251 256 (by norm_num) (by norm_num)).2 (by norm_num),

  calc sqrt 2008 * log 2008 = sqrt (4 * 502) * log 2008 : by norm_num
  ... = (sqrt 4 * sqrt 502) * log 2008 : by rw @sqrt_mul 4 (by linarith) 502
  ... = (2 * sqrt 502) * log 2008 : by rw sqrt_four
  ... = (2 * sqrt 502) * (log (8 * 251)) : by norm_num
  ... = (2 * sqrt 502) * (log 8 + log 251) : by rw @log_mul 8 251 (by norm_num) (by norm_num)
  ... ≤ (2 * sqrt 502) * (log 8 + log 256) : by sorry
  ... ≤ (2 * sqrt 502) * (log (2 ^ 3) + log 256) : by rw eight_pow
  ... = (2 * sqrt 502) * (log (2 ^ 3) + log (2 ^ 8)) : by rw two_fifty_six_pow
  ... = (2 * sqrt 502) * (3 * log 2 + log (2 ^ 8)) : by sorry
  ... = (2 * sqrt 502) * (3 * log 2 + 8 * log 2) : by sorry
  ... = (2 * sqrt 502) * (11 * log 2) : by ring
  ... = (11 * sqrt 502) * (2 * log 2) : by ring
  ... < 250 * (2 * log 2) : by sorry -- use r here
  ... = 250 * (log (2 ^ 2)) : by sorry
  ... = 250 * log 4 : by norm_num
end

lemma fff_has_root : ∃ (x : ℝ), (1 ≤ x ∧ x ≤ 250) ∧ fff x = 0 :=
begin
  have r : (1 : ℝ) ≤ 250 := by norm_num,
  have fff_continuous' : continuous_on fff (Icc 1 250),
    {
      -- This is trivial: Icc 1 250 is a subset of Ici 1
      sorry,
    },
  have intermediate := intermediate_value_Icc r fff_continuous',
  have t : (0 : ℝ) ∈ Icc (fff 1) (fff 250),
    { simp only [mem_Icc],
      split,
      { exact (le_of_lt fff_one), },
      { exact (le_of_lt fff_250), }, },
  simpa using (intermediate t),
end

lemma linear_dominates_sqrt_log (x : ℝ) (hx : 250 ≤ x)
  : sqrt (8 * x + 8) * log (8 * x + 8) ≤ x * log 4 :=
begin
  suffices: 0 ≤ fff x,
    { unfold fff at this,
      simpa using this, },
  have conv : convex (Ici (250 : ℝ)) := convex_Ici _,
  have t : ∀ (x : ℝ), x ∈ interior (Ici (250 : ℝ)) → 0 ≤ deriv fff x,
    { intros x x_in_interior,
      have x_big : 250 < x, by simpa using x_in_interior,
      rw @fff'_is_deriv x (by linarith),
      exact deriv_nonneg (by linarith), },
  have x_in_ici : x ∈ Ici (250 : ℝ) := by simpa using hx,
  rcases fff_has_root with ⟨c, ⟨⟨c_big, c_small⟩, c_is_root⟩⟩,
  have c_in_ici : c ∈ Ici (250 : ℝ),
    { sorry, },
  have: fff c ≤ fff x :=
    convex.mono_of_deriv_nonneg conv (fff_continuous (by linarith)) (fff_differentiable (by linarith)) t c x c_in_ici x_in_ici (by linarith),
  linarith,
end

lemma pow_beats_pow_2 (n : ℕ) (n_large : 250 ≤ n) : (8 * n + 8) ^ nat.sqrt (8 * n + 8) ≤ 4 ^ n :=
begin
  apply (@nat.cast_le ℝ _ _ _ _).1,
  calc ↑((8 * n + 8) ^ nat.sqrt (8 * n + 8))
      ≤ (↑(8 * n + 8) ^ real.sqrt (↑(8 * n + 8))) :
          begin
            rw pow_coe,
            apply real.rpow_le_rpow_of_exponent_le,
              {
                apply nat.one_le_cast.2,
                linarith,
                exact real.nontrivial,
              },
              {apply nat_sqrt_le_real_sqrt,},
          end
  ... ≤ ↑(4 ^ n) :
          begin
            apply (@real.log_le_log _ (↑(4 ^ n)) _ (by norm_num)).1,
            { rw real.log_rpow _,
              { rw pow_coe,
                rw real.log_rpow,
                { norm_cast,
                  norm_num,
                  apply linear_dominates_sqrt_log,
                  norm_cast,
                  exact n_large, },
                { norm_num, },
              },
              { norm_cast,
                linarith,},
            },
            { norm_num,
              refine rpow_pos_of_pos _ _,
              { norm_cast,
                linarith,},
            },
          end,
end

lemma power_conversion_2 (n : ℕ) (n_large : 1003 < n) : (2 * n) ^ nat.sqrt (2 * n) ≤ 4 ^ (n / 4) :=
begin
  have : 250 ≤ n / 4,
    { cases le_or_gt 250 (n / 4),
      { exact h, },
      { have r : n < n :=
          calc n = 4 * (n / 4) + (n % 4) : (nat.div_add_mod n 4).symm
            ... < 4 * 250 + (n % 4) : add_lt_add_right ((mul_lt_mul_left (nat.succ_pos 3)).2 h) _
            ... < 4 * 250 + 4 : add_lt_add_left (nat.mod_lt n (by linarith)) _
            ... = 1004 : by norm_num
            ... ≤ n : by linarith,
        exfalso,
        exact lt_irrefl _ r, }, },
  have rem_small : (n % 4) < 4 := nat.mod_lt n (nat.succ_pos 3),
  calc (2 * n) ^ nat.sqrt (2 * n) = (2 * (4 * (n / 4) + (n % 4))) ^ nat.sqrt (2 * (4 * (n / 4) + (n % 4))) : by rw nat.div_add_mod n 4
  ... ≤ (2 * (4 * (n / 4) + (n % 4))) ^ nat.sqrt (8 * (n / 4) + 8) :
              begin
                apply pow_le_pow,
                -- squeeze_simp,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                suffices : 1 ≤ 8 * (n / 4),
                  exact le_add_right this,
                linarith,
                apply nat.sqrt_le_sqrt,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                -- squeeze_simp,
                linarith,
              end
  ... ≤ (8 * (n / 4) + 8) ^ nat.sqrt (8 * (n / 4) + 8) :
              begin
                apply (nat.pow_le_iff_le_left _).2,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                linarith,
                apply nat.le_sqrt.2,
                suffices : 1 * 1 ≤ 8,
                  exact le_add_left this,
                norm_num,
              end
  ... ≤ 4 ^ (n / 4) : pow_beats_pow_2 (n / 4) (by linarith),
end


lemma fooo (n : ℕ) (n_pos : 1 ≤ n) : n / 15 + n / 4 + (2 * n / 3 + 1) ≤ n :=
begin
  suffices: n / 15 + n / 4 + 2 * n / 3 < n, by linarith,
  have s1 : (n / 15) * 15 ≤ n := nat.div_mul_le_self n 15,
  have s2 : (n / 4) * 4 ≤ n := nat.div_mul_le_self n 4,
  have s3 : (2 * n / 3) * 3 ≤ 2 * n := nat.div_mul_le_self (2 * n) 3,
  suffices: (n / 15 + n / 4 + 2 * n / 3) * 60 < n * 60, by linarith,
  calc (n / 15 + n / 4 + 2 * n / 3) * 60
      = n / 15 * 15 * 4 + n / 4 * 4 * 15 + 2 * n / 3 * 3 * 20 : by ring
  ... ≤ n * 4 + n * 15 + 2 * n * 20 : by linarith [s1, s2, s3]
  ... < n * 60 : by linarith,
end


lemma false_inequality_is_false {n : ℕ} (n_large : 1003 < n) : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) → false :=
begin
  rw imp_false,
  rw not_lt,
  calc (2 * n + 1) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1)
       ≤ (4 ^ (n / 15)) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_right ((2 * n) ^ nat.sqrt (2 * n))),
            apply power_conversion_1,
            linarith,
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
            exact fooo n (by linarith),
          end
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
    exact nat.le_sqrt'.symm, },

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
      { have : i ≤ nat.sqrt (2 * n) := nat.le_sqrt'.mpr hyp.2,
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

lemma bertrand_eventually (n : nat) (n_big : 1003 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
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
    exact false_inequality_is_false n_big false_inequality,
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
cases lt_or_le 1003 n,
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
