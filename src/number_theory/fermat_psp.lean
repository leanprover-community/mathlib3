/-
Copyright (c) 2022 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/
import data.nat.prime
import field_theory.finite.basic
import order.filter.cofinite

/-!
# Fermat Pseudoprimes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define Fermat pseudoprimes: composite numbers that pass the Fermat primality test.
A natural number `n` passes the Fermat primality test to base `b` (and is therefore deemed a
"probable prime") if `n` divides `b ^ (n - 1) - 1`. `n` is a Fermat pseudoprime to base `b` if `n`
is a composite number that passes the Fermat primality test to base `b` and is coprime with `b`.

Fermat pseudoprimes can also be seen as composite numbers for which Fermat's little theorem holds
true.

Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined
in this file).

## Main Results

The main definitions for this file are

- `fermat_psp.probable_prime`: A number `n` is a probable prime to base `b` if it passes the Fermat
  primality test; that is, if `n` divides `b ^ (n - 1) - 1`
- `fermat_psp`: A number `n` is a pseudoprime to base `b` if it is a probable prime to base `b`, is
  composite, and is coprime with `b` (this last condition is automatically true if `n` divides
  `b ^ (n - 1) - 1`, but some sources include it in the definition).

Note that all composite numbers are pseudoprimes to base 0 and 1, and that the definiton of
`probable_prime` in this file implies that all numbers are probable primes to bases 0 and 1, and
that 0 and 1 are probable primes to any base.

The main theorems are
- `fermat_psp.exists_infinite_pseudoprimes`: there are infinite pseudoprimes to any base `b ≥ 1`
-/

/--
`n` is a probable prime to base `b` if `n` passes the Fermat primality test; that is, `n` divides
`b ^ (n - 1) - 1`.
This definition implies that all numbers are probable primes to base 0 or 1, and that 0 and 1 are
probable primes to any base.
-/
def fermat_psp.probable_prime (n b : ℕ) : Prop := n ∣ b ^ (n - 1) - 1

/--
`n` is a Fermat pseudoprime to base `b` if `n` is a probable prime to base `b` and is composite. By
this definition, all composite natural numbers are pseudoprimes to base 0 and 1. This definition
also permits `n` to be less than `b`, so that 4 is a pseudoprime to base 5, for example.
-/
def fermat_psp (n b : ℕ) : Prop := fermat_psp.probable_prime n b ∧ ¬n.prime ∧ 1 < n

namespace fermat_psp

instance decidable_probable_prime (n b : ℕ) : decidable (probable_prime n b) :=
nat.decidable_dvd _ _

instance decidable_psp (n b : ℕ) : decidable (fermat_psp n b) := and.decidable

/--
If `n` passes the Fermat primality test to base `b`, then `n` is coprime with `b`, assuming that
`n` and `b` are both positive.
-/
lemma coprime_of_probable_prime {n b : ℕ} (h : probable_prime n b) (h₁ : 1 ≤ n) (h₂ : 1 ≤ b) :
  nat.coprime n b :=
begin
  by_cases h₃ : 2 ≤ n,

  { -- To prove that `n` is coprime with `b`, we we need to show that for all prime factors of `n`,
    -- we can derive a contradiction if `n` divides `b`.
    apply nat.coprime_of_dvd,

    -- If `k` is a prime number that divides both `n` and `b`, then we know that `n = m * k` and
    -- `b = j * k` for some natural numbers `m` and `j`. We substitute these into the hypothesis.
    rintros k hk ⟨m, rfl⟩ ⟨j, rfl⟩,

    -- Because prime numbers do not divide 1, it suffices to show that `k ∣ 1` to prove a
    -- contradiction
    apply nat.prime.not_dvd_one hk,

    -- Since `n` divides `b ^ (n - 1) - 1`, `k` also divides `b ^ (n - 1) - 1`
    replace h := dvd_of_mul_right_dvd h,

    -- Because `k` divides `b ^ (n - 1) - 1`, if we can show that `k` also divides `b ^ (n - 1)`,
    -- then we know `k` divides 1.
    rw [nat.dvd_add_iff_right h, nat.sub_add_cancel (nat.one_le_pow _ _ h₂)],

    -- Since `k` divides `b`, `k` also divides any power of `b` except `b ^ 0`. Therefore, it
    -- suffices to show that `n - 1` isn't zero. However, we know that `n - 1` isn't zero because we
    -- assumed `2 ≤ n` when doing `by_cases`.
    refine dvd_of_mul_right_dvd (dvd_pow_self (k * j) _),
    linarith },

  -- If `n = 1`, then it follows trivially that `n` is coprime with `b`.
  { rw (show n = 1, by linarith),
    norm_num }
end

lemma probable_prime_iff_modeq (n : ℕ) {b : ℕ} (h : 1 ≤ b) :
  probable_prime n b ↔ b ^ (n - 1) ≡ 1 [MOD n] :=
begin
  have : 1 ≤ b ^ (n - 1) := one_le_pow_of_one_le h (n - 1), -- For exact_mod_cast
  rw nat.modeq.comm,
  split,
  { intro h₁,
    apply nat.modeq_of_dvd,
    exact_mod_cast h₁, },
  { intro h₁,
    exact_mod_cast nat.modeq.dvd h₁, },
end

/--
If `n` is a Fermat pseudoprime to base `b`, then `n` is coprime with `b`, assuming that `b` is
positive.

This lemma is a small wrapper based on `coprime_of_probable_prime`
-/
lemma coprime_of_fermat_psp {n b : ℕ} (h : fermat_psp n b) (h₁ : 1 ≤ b) : nat.coprime n b :=
begin
  rcases h with ⟨hp, hn₁, hn₂⟩,
  exact coprime_of_probable_prime hp (by linarith) h₁,
end

/--
All composite numbers are Fermat pseudoprimes to base 1.
-/
lemma base_one {n : ℕ} (h₁ : 1 < n) (h₂ : ¬n.prime) : fermat_psp n 1 :=
begin
  refine ⟨show n ∣ 1 ^ (n - 1) - 1, from _, h₂, h₁⟩,
  exact (show 0 = 1 ^ (n - 1) - 1, by norm_num) ▸ dvd_zero n,
end

-- Lemmas that are needed to prove statements in this file, but aren't directly related to Fermat
-- pseudoprimes
section helper_lemmas

private lemma pow_gt_exponent {a : ℕ} (b : ℕ) (h : 2 ≤ a) : b < a ^ b :=
lt_of_lt_of_le (nat.lt_two_pow b) $ nat.pow_le_pow_of_le_left h _

private lemma a_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : 2 ≤ (a ^ b - 1) / (a - 1) :=
begin
  change 1 < _,
  have h₁ : a - 1 ∣ a ^ b - 1 := by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow a 1 b,
  rw [nat.lt_div_iff_mul_lt h₁, mul_one, tsub_lt_tsub_iff_right (nat.le_of_succ_le ha)],
  convert pow_lt_pow (nat.lt_of_succ_le ha) hb,
  rw pow_one
end

private lemma b_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : 2 ≤ (a ^ b + 1) / (a + 1) :=
begin
  rw nat.le_div_iff_mul_le (nat.zero_lt_succ _),
  apply nat.succ_le_succ,
  calc 2 * a + 1 ≤ a ^ 2 * a : by nlinarith
             ... = a ^ 3     : by rw pow_succ' a 2
             ... ≤ a ^ b     : pow_le_pow (nat.le_of_succ_le ha) hb
end

private lemma AB_id_helper (b p : ℕ) (hb : 2 ≤ b) (hp : odd p)
  : (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) :=
begin
  have q₁ : b - 1 ∣ b ^ p - 1 := by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow b 1 p,
  have q₂ : b + 1 ∣ b ^ p + 1 := by simpa only [one_pow] using hp.nat_add_dvd_pow_add_pow b 1,
  convert nat.div_mul_div_comm q₁ q₂; rw [mul_comm (_ - 1), ←nat.sq_sub_sq],
  { ring_exp },
  { simp }
end

/--
Used in the proof of `psp_from_prime_psp`
-/
private lemma bp_helper {b p : ℕ} (hb : 0 < b) (hp : 1 ≤ p) :
  b ^ (2 * p) - 1 - (b ^ 2 - 1) =  b * (b ^ (p - 1) - 1) * (b ^ p + b) :=
have hi_bsquared : 1 ≤ b ^ 2 := nat.one_le_pow _ _ hb,
calc b ^ (2 * p) - 1 - (b ^ 2 - 1) = b ^ (2 * p) - (1 + (b ^ 2 - 1)) : by rw nat.sub_sub
      ... = b ^ (2 * p) - (1 + b ^ 2 - 1)           : by rw nat.add_sub_assoc hi_bsquared
      ... = b ^ (2 * p) - (b ^ 2)                   : by rw nat.add_sub_cancel_left
      ... = b ^ (p * 2) - (b ^ 2)                   : by rw mul_comm
      ... = (b ^ p) ^ 2 - (b ^ 2)                   : by rw pow_mul
      ... = (b ^ p + b) * (b ^ p - b)               : by rw nat.sq_sub_sq
      ... = (b ^ p - b) * (b ^ p + b)               : by rw mul_comm
      ... = (b ^ (p - 1 + 1) - b) * (b ^ p + b)     : by rw nat.sub_add_cancel hp
      ... = (b * b ^ (p - 1) - b) * (b ^ p + b)     : by rw pow_succ
      ... = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) : by rw mul_one
      ... = b * (b ^ (p - 1) - 1) * (b ^ p + b)     : by rw nat.mul_sub_left_distrib

end helper_lemmas

/--
Given a prime `p` which does not divide `b * (b ^ 2 - 1)`, we can produce a number `n` which is
larger than `p` and pseudoprime to base `b`. We do this by defining
`n = ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1))`

The primary purpose of this definition is to help prove `exists_infinite_pseudoprimes`. For a proof
that `n` is actually pseudoprime to base `b`, see `psp_from_prime_psp`, and for a proof that `n` is
greater than `p`, see `psp_from_prime_gt_p`.

This lemma is intended to be used when `2 ≤ b`, `2 < p`, `p` is prime, and `¬p ∣ b * (b ^ 2 - 1)`,
because those are the hypotheses for `psp_from_prime_psp`.
-/
private def psp_from_prime (b : ℕ) (p : ℕ) : ℕ := (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

/--
This is a proof that the number produced using `psp_from_prime` is actually pseudoprime to base `b`.
The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.

We use <https://primes.utm.edu/notes/proofs/a_pseudoprimes.html> as a rough outline of the proof.
-/
private lemma psp_from_prime_psp {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.prime)
  (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b * (b ^ 2 - 1)) :
  fermat_psp (psp_from_prime b p) b :=
begin
  unfold psp_from_prime,
  set A := (b ^ p - 1) / (b - 1),
  set B := (b ^ p + 1) / (b + 1),

  -- Inequalities
  have hi_A : 1 < A := a_id_helper (nat.succ_le_iff.mp b_ge_two) (nat.prime.one_lt p_prime),
  have hi_B : 1 < B := b_id_helper (nat.succ_le_iff.mp b_ge_two) p_gt_two,
  have hi_AB : 1 < A * B := one_lt_mul'' hi_A hi_B,
  have hi_b : 0 < b := by linarith,
  have hi_p : 1 ≤ p := nat.one_le_of_lt p_gt_two,
  have hi_bsquared : 0 < b ^ 2 - 1 := by nlinarith [nat.one_le_pow 2 b hi_b],
  have hi_bpowtwop : 1 ≤ b ^ (2 * p) := nat.one_le_pow (2 * p) b hi_b,
  have hi_bpowpsubone : 1 ≤ b ^ (p - 1) := nat.one_le_pow (p - 1) b hi_b,

  -- Other useful facts
  have p_odd : odd p := p_prime.odd_of_ne_two p_gt_two.ne.symm,
  have AB_not_prime : ¬nat.prime (A * B) := nat.not_prime_mul hi_A hi_B,
  have AB_id : A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := AB_id_helper _ _ b_ge_two p_odd,
  have hd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1,
  { simpa only [one_pow, pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 p },

  -- We know that `A * B` is not prime, and that `1 < A * B`. Since two conditions of being
  -- pseudoprime are satisfied, we only need to show that `A * B` is probable prime to base `b`
  refine ⟨_, AB_not_prime, hi_AB⟩,

  -- Used to prove that `2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1)`.
  have ha₁ : (b ^ 2 - 1) * (A * B - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b),
  { apply_fun (λ x, x * (b ^ 2 - 1)) at AB_id,
    rw nat.div_mul_cancel hd at AB_id,
    apply_fun (λ x, x - (b ^ 2 - 1)) at AB_id,
    nth_rewrite 1 ←one_mul (b ^ 2 - 1) at AB_id,
    rw [←nat.mul_sub_right_distrib, mul_comm] at AB_id,
    rw AB_id,
    exact bp_helper hi_b hi_p },
  -- If `b` is even, then `b^p` is also even, so `2 ∣ b^p + b`
  -- If `b` is odd, then `b^p` is also odd, so `2 ∣ b^p + b`
  have ha₂ : 2 ∣ b ^ p + b,
  { by_cases h : even b,
    { replace h : 2 ∣ b := even_iff_two_dvd.mp h,
      have : p ≠ 0 := by linarith,
      have : 2 ∣ b^p := dvd_pow h this,
      exact dvd_add this h },
    { have h : odd b := nat.odd_iff_not_even.mpr h,
      have : odd (b ^ p) := odd.pow h,
      have : even (b ^ p + b) := odd.add_odd this h,
      exact even_iff_two_dvd.mp this } },
  -- Since `b` isn't divisible by `p`, `b` is coprime with `p`. we can use Fermat's Little Theorem
  -- to prove this.
  have ha₃ : p ∣ b ^ (p - 1) - 1,
  { have : ¬p ∣ b := mt (assume h : p ∣ b, dvd_mul_of_dvd_left h _) not_dvd,
    have : p.coprime b := or.resolve_right (nat.coprime_or_dvd_of_prime p_prime b) this,
    have : is_coprime (b : ℤ) ↑p := this.symm.is_coprime,
    have : ↑b ^ (p - 1) ≡ 1 [ZMOD ↑p] := int.modeq.pow_card_sub_one_eq_one p_prime this,
    have : ↑p ∣ ↑b ^ (p - 1) - ↑1 := int.modeq.dvd (int.modeq.symm this),
    exact_mod_cast this },
  -- Because `p - 1` is even, there is a `c` such that `2 * c = p - 1`. `nat_sub_dvd_pow_sub_pow`
  -- implies that `b ^ c - 1 ∣ (b ^ c) ^ 2 - 1`, and `(b ^ c) ^ 2 = b ^ (p - 1)`.
  have ha₄ : b ^ 2 - 1 ∣ b ^ (p - 1) - 1,
  { cases p_odd with k hk,
    have : 2 ∣ p - 1 := ⟨k, by simp [hk]⟩,
    cases this with c hc,
    have : b ^ 2 - 1 ∣ (b ^ 2) ^ c - 1 :=
      by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c,
    have : b ^ 2 - 1 ∣ b ^ (2 * c) - 1 := by rwa ←pow_mul at this,
    rwa ←hc at this },
  -- Used to prove that `2 * p` divides `A * B - 1`
  have ha₅ : 2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1),
  { suffices q : 2 * p * (b ^ 2 - 1) ∣ b * (b ^ (p - 1) - 1) * (b ^ p + b),
    { rwa ha₁ },
    -- We already proved that `b ^ 2 - 1 ∣ b ^ (p - 1) - 1`.
    -- Since `2 ∣ b ^ p + b` and `p ∣ b ^ p + b`, if we show that 2 and p are coprime, then we
    -- know that `2 * p ∣ b ^ p + b`
    have q₁ : nat.coprime p (b ^ 2 - 1),
    { have q₂ : ¬p ∣ b ^ 2 - 1,
      { rw mul_comm at not_dvd,
        exact mt (assume h : p ∣ b ^ 2 - 1, dvd_mul_of_dvd_left h _) not_dvd },
      exact (nat.prime.coprime_iff_not_dvd p_prime).mpr q₂ },
    have q₂ : p * (b ^ 2 - 1) ∣ b ^ (p - 1) - 1 := nat.coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄,
    have q₃ : p * (b ^ 2 - 1) * 2 ∣ (b ^ (p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂,
    have q₄ : p * (b ^ 2 - 1) * 2 ∣ b * ((b ^ (p - 1) - 1) * (b ^ p + b)),
      from dvd_mul_of_dvd_right q₃ _,
    rwa [mul_assoc, mul_comm, mul_assoc b] },
  have ha₆ : 2 * p ∣ A * B - 1,
  { rw mul_comm at ha₅,
    exact nat.dvd_of_mul_dvd_mul_left hi_bsquared ha₅ },
  -- `A * B` divides `b ^ (2 * p) - 1` because `A * B * (b ^ 2 - 1) = b ^ (2 * p) - 1`.
  -- This can be proven by multiplying both sides of `AB_id` by `b ^ 2 - 1`.
  have ha₇ : A * B ∣ b ^ (2 * p) - 1,
  { use b ^ 2 - 1,
    have : A * B * (b ^ 2 - 1) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) * (b ^ 2 - 1),
      from congr_arg (λ x : ℕ, x * (b ^ 2 - 1)) AB_id,
    simpa only [add_comm, nat.div_mul_cancel hd, nat.sub_add_cancel hi_bpowtwop] using this.symm },
  -- Since `2 * p ∣ A * B - 1`, there is a number `q` such that `2 * p * q = A * B - 1`.
  -- By `nat_sub_dvd_pow_sub_pow`, we know that `b ^ (2 * p) - 1 ∣ b ^ (2 * p * q) - 1`.
  -- This means that `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  cases ha₆ with q hq,
  have ha₈ : b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1 :=
    by simpa only [one_pow, pow_mul, hq] using nat_sub_dvd_pow_sub_pow _ 1 q,
  -- We have proved that `A * B ∣ b ^ (2 * p) - 1` and `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  -- Therefore, `A * B ∣ b ^ (A * B - 1) - 1`.
  exact dvd_trans ha₇ ha₈
end

/--
This is a proof that the number produced using `psp_from_prime` is greater than the prime `p` used
to create it. The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.
-/
private lemma psp_from_prime_gt_p {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.prime)
  (p_gt_two : 2 < p) :
  p < psp_from_prime b p :=
begin
  unfold psp_from_prime,
  set A := (b ^ p - 1) / (b - 1),
  set B := (b ^ p + 1) / (b + 1),
  rw show A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1),
    from AB_id_helper _ _ b_ge_two (p_prime.odd_of_ne_two p_gt_two.ne.symm),
  have AB_dvd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1,
    by simpa only [one_pow, pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 p,

  suffices h : p * (b ^ 2 - 1) < b ^ (2 * p) - 1,
  { have h₁ : (p * (b ^ 2 - 1)) / (b ^ 2 - 1) < (b ^ (2 * p) - 1) / (b ^ 2 - 1),
      from nat.div_lt_div_of_lt_of_dvd AB_dvd h,
    have h₂ : 0 < b ^ 2 - 1,
      by linarith [show 3 ≤ b ^ 2 - 1, from le_tsub_of_add_le_left (show 4 ≤ b ^ 2, by nlinarith)],
    rwa nat.mul_div_cancel _ h₂ at h₁ },

  rw [nat.mul_sub_left_distrib, mul_one, pow_mul],
  nth_rewrite_rhs 0 ←nat.sub_add_cancel (show 1 ≤ p, by linarith),
  rw pow_succ (b ^ 2),
  suffices h : p * b ^ 2 < b ^ 2 * (b ^ 2) ^ (p - 1),
  { apply gt_of_ge_of_gt,
    { exact tsub_le_tsub_left (show 1 ≤ p, by linarith) (b ^ 2 * (b ^ 2) ^ (p - 1)) },
    { have : p ≤ p * b ^ 2 := nat.le_mul_of_pos_right (show 0 < b ^ 2, by nlinarith),
      exact tsub_lt_tsub_right_of_le this h } },

  suffices h : p < (b ^ 2) ^ (p - 1),
  { rw mul_comm (b ^ 2),
    have : 4 ≤ b ^ 2 := by nlinarith,
    have : 0 < b ^ 2 := by linarith,
    exact mul_lt_mul_of_pos_right h this },

  rw [←pow_mul, nat.mul_sub_left_distrib, mul_one],
  have : 2 ≤ 2 * p - 2 := le_tsub_of_add_le_left (show 4 ≤ 2 * p, by linarith),
  have : 2 + p ≤ 2 * p := by linarith,
  have : p ≤ 2 * p - 2 := le_tsub_of_add_le_left this,
  exact nat.lt_of_le_of_lt this (pow_gt_exponent _ b_ge_two)
end

/--
For all positive bases, there exist Fermat infinite pseudoprimes to that base.
Given in this form: for all numbers `b ≥ 1` and `m`, there exists a pseudoprime `n` to base `b` such
that `m ≤ n`. This form is similar to `nat.exists_infinite_primes`.
-/
theorem exists_infinite_pseudoprimes {b : ℕ} (h : 1 ≤ b) (m : ℕ) : ∃ n : ℕ, fermat_psp n b ∧ m ≤ n
:=
begin
  by_cases b_ge_two : 2 ≤ b,
  -- If `2 ≤ b`, then because there exist infinite prime numbers, there is a prime number p such
  -- `m ≤ p` and `¬p ∣ b*(b^2 - 1)`. We pick a prime number `b*(b^2 - 1) + 1 + m ≤ p` because we
  -- automatically know that `p` is greater than m and that it does not divide `b*(b^2 - 1)`
  -- (because `p` can't divide a number less than `p`).
  -- From `p`, we can use the lemmas we proved earlier to show that
  -- `((b^p - 1)/(b - 1)) * ((b^p + 1)/(b + 1))` is a pseudoprime to base `b`.
  { have h := nat.exists_infinite_primes (b * (b ^ 2 - 1) + 1 + m),
    cases h with p hp,
    cases hp with hp₁ hp₂,
    have h₁ : 0 < b := pos_of_gt (nat.succ_le_iff.mp b_ge_two),
    have h₂ : 4 ≤ b ^ 2 := pow_le_pow_of_le_left' b_ge_two 2,
    have h₃ : 0 < b ^ 2 - 1 := tsub_pos_of_lt (gt_of_ge_of_gt h₂ (by norm_num)),
    have h₄ : 0 < b * (b ^ 2 - 1) := mul_pos h₁ h₃,
    have h₅ : b * (b ^ 2 - 1) < p := by linarith,
    have h₆ : ¬p ∣ b * (b ^ 2 - 1) := nat.not_dvd_of_pos_of_lt h₄ h₅,
    have h₇ : b ≤ b * (b ^ 2 - 1) := nat.le_mul_of_pos_right h₃,
    have h₈ : 2 ≤ b * (b ^ 2 - 1) := le_trans b_ge_two h₇,
    have h₉ : 2 < p := gt_of_gt_of_ge h₅ h₈,
    have h₁₀ := psp_from_prime_gt_p b_ge_two hp₂ h₉,
    use psp_from_prime b p,
    split,
    { exact psp_from_prime_psp b_ge_two hp₂ h₉ h₆ },
    { exact le_trans (show m ≤ p, by linarith) (le_of_lt h₁₀) } },
  -- If `¬2 ≤ b`, then `b = 1`. Since all composite numbers are pseudoprimes to base 1, we can pick
  -- any composite number greater than m. We choose `2 * (m + 2)` because it is greater than `m` and
  -- is composite for all natural numbers `m`.
  { have h₁ : b = 1 := by linarith,
    rw h₁,
    use 2 * (m + 2),
    have : ¬nat.prime (2 * (m + 2)) := nat.not_prime_mul (by norm_num) (by norm_num),
    exact ⟨base_one (by linarith) this, by linarith⟩ }
end

theorem frequently_at_top_fermat_psp {b : ℕ} (h : 1 ≤ b) : ∃ᶠ n in filter.at_top, fermat_psp n b :=
begin
  -- Based on the proof of `nat.frequently_at_top_modeq_one`
  refine filter.frequently_at_top.2 (λ n, _),
  obtain ⟨p, hp⟩ := exists_infinite_pseudoprimes h n,
  exact ⟨p, hp.2, hp.1⟩
end

/--
Infinite set variant of `exists_infinite_pseudoprimes`
-/
theorem infinite_set_of_prime_modeq_one {b : ℕ} (h : 1 ≤ b) :
  set.infinite {n : ℕ | fermat_psp n b} :=
nat.frequently_at_top_iff_infinite.mp (frequently_at_top_fermat_psp h)

end fermat_psp
