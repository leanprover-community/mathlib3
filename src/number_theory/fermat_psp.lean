/-
Copyright (c) 2022 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/
import data.nat.prime
import field_theory.finite.basic

/-!
# Fermat Pseudoprimes

In this file we define Fermat pseudoprimes: composite numbers that pass the Fermat primality test.
A natural number n passes the Fermat primality test to base b (and is therefore deemed a "probable
prime") if n divides `b^(n - 1) - 1`. n is a Fermat pseudoprime to base b if n is a composite number
that passes the Fermat primality test to base b and is coprime with b.

Fermat pseudoprimes can also be seen as composite numbers for which Fermat's little theorem holds
true.

## Main Results

The main definitions for this file are

- `fermat_psp.probable_prime`: A number n is a probable prime to base b if it passes the Fermat
  primality test; that is, b divides b^(n - 1) - 1
- `fermat_psp`: A number n is a pseudoprime to base b if it is a probable prime to base b, is
  composite, and is coprime with b

Note that all composite numbers are pseudoprimes to base 0 and 1, and that the definiton of
probable_prime in this file implies that all numbers are probable primes to bases 0 and 1, and 0 and
1 are probable primes to any base.

The main theorems are
- `fermat_psp.exists_infinite_pseudoprimes`: there are infinite pseudoprimes to any base b ≥ 1
-/

/--
`n` is a probable prime to base `b` if `n` passes the Fermat primality test; that is, `n` divides
`b^(n - 1) - 1`.
This definition implies that all numbers are probable primes to base 0 or 1, and that 0 and 1 are
probable primes to any base.
-/
def fermat_psp.probable_prime (n b : ℕ) : Prop := n ∣ b^(n - 1) - 1

/--
`n` is a Fermat pseudoprime to base `b` if `n` is a probable prime to base `b` and is composite. By
this definition, all composite natural numbers are pseudoprimes to base 0 and 1. This definition
also permits `n` to be less than `b`, so that 4 is a pseudoprime to base 5, for example.
-/
def fermat_psp (n b : ℕ) : Prop := fermat_psp.probable_prime n b ∧ ¬nat.prime n ∧ 1 < n

namespace fermat_psp

instance decidable_probable_prime (n b : ℕ) : decidable (probable_prime n b) :=
nat.decidable_dvd _ _

instance decidable_psp (n b : ℕ) : decidable (fermat_psp n b) := and.decidable

/--
If `n` passes the Fermat primality test to base `b`, then `n` is coprime with `b`, assuming that
`n` and `b` are both positive.
-/
lemma coprime_of_probable_prime (n b : ℕ) (h : probable_prime n b) (h₁ : 1 ≤ n) (h₂ : 1 ≤ b) :
  nat.coprime n b :=
begin
  unfold probable_prime at h,
  by_cases h₃ : 2 ≤ n,

  { -- To prove that `n` is coprime with `b`, we we need to show that for all prime factors of `n`,
    -- we can derive a contradiction if `n` divides `b`.
    refine nat.coprime_of_dvd _,
    intros k hk hn hb,

    -- If `k` is a prime number that divides both `n` and `b`, then we know that `n = m * k` and
    -- `b = j * k` for some natural numbers `m` and `j`. We substitute these into the hypothesis.
    generalize hm : n / k = m,
    generalize hj : b / k = j,
    have : m * k ∣ b ^ (n - 1) - 1 := by rwa [←hm, nat.div_mul_cancel hn],
    have : m * k ∣ (j * k) ^ (n - 1) - 1 := by rwa [←hj, nat.div_mul_cancel hb],

    -- Inequalities that will be useful later in the proof
    have q₁ : 1 ≤ j * k,
    { rw [←hj, nat.div_mul_cancel]; assumption },
    have q₂ : 1 ≤ (j * k) ^ (n - 1) := one_le_pow_of_one_le q₁ (n - 1),
    have q₃ : 1 ≤ n - 1,
    { have : n - 1 + 1 = n := nat.sub_add_cancel (show 1 ≤ n, by linarith),
      linarith },
    have q₄ : (n - 1) - 1 + 1 = n - 1 := nat.sub_add_cancel q₃,

    -- Follows from the fact that `m * k ∣ (j * k) ^ (n - 1) - 1`
    have : k ∣ (j * k) ^ (n - 1) - 1 := dvd_of_mul_left_dvd this,

    -- Follows from the fact that `2 ≤ n`
    have q : k ∣ (j * k) ^ (n - 1),
    { rw mul_pow,
      apply dvd_mul_of_dvd_right,
      rw [←q₄, pow_succ],
      exact dvd.intro _ rfl },

    -- Since we know that `k` divides both `(j * k) ^ (n - 1)` and `(j * k) ^ (n - 1) - 1`,
    -- it must divide their difference, so `k ∣ 1`. This contradicts the assumption that `k` is a
    -- prime.
    have : k ∣ (j * k) ^ (n - 1) - ((j * k) ^ (n - 1) - 1) := nat.dvd_sub' q this,
    rw nat.sub_sub_self q₂ at this,
    exact nat.prime.not_dvd_one hk this },

  -- If n = 1, then it follows trivially that n is coprime with b.
  { have : n = 1 := by linarith,
    rw this,
    norm_num }
end

lemma probable_prime_iff_modeq (n : ℕ) {b : ℕ} (h : 1 ≤ b) :
  probable_prime n b ↔ b^(n - 1) ≡ 1 [MOD n] :=
begin
  have : 1 ≤ b ^ (n - 1) := one_le_pow_of_one_le h (n - 1), -- For exact_mod_cast
  split,
  { intro h₁,
    apply nat.modeq_of_dvd,
    have h₂ : ↑n ∣ ↑(b ^ (n - 1)) - (1 : ℤ) := by exact_mod_cast h₁,
    have h₃ : - (↑(b ^ (n - 1)) - (1 : ℤ)) = ((↑1 : ℤ) - ↑(b ^ (n - 1))) := by simp,
    exact h₃ ▸ (dvd_neg _ _).mpr h₂ },
  { intro h₁,
    have h₂ : ↑n ∣ ↑(b ^ (n - 1)) - (1 : ℤ) := nat.modeq.dvd h₁.symm,
    exact_mod_cast h₂ }
end

/--
If `n` is a Fermat pseudoprime to base `b`, then `n` is coprime with `b`, assuming that `b` is
positive.

This lemma is a small wrapper based on `coprime_of_probable_prime`
-/
lemma coprime_of_fermat_psp (n b : ℕ) (h : fermat_psp n b) (h₁ : 1 ≤ b) : nat.coprime n b :=
begin
  cases h with hp hn,
  cases hn with hn₁ hn₂,
  exact coprime_of_probable_prime n b hp (by linarith) h₁,
end

/--
All composite numbers are Fermat pseudoprimes to base 1.
-/
lemma pseudoprime_of_base_one (n : ℕ) (h₁ : 1 < n) (h₂ : ¬nat.prime n) : fermat_psp n 1 :=
begin
  split,
  { have h : 0 = 1^(n - 1) - 1 := by norm_num,
    show n ∣ 1^(n - 1) - 1, from h ▸ (dvd_zero n) },
  { exact ⟨h₂, h₁⟩ }
end

private lemma odd_of_prime_gt_two (p : ℕ) (h : nat.prime p) (hp : 2 < p) : odd p :=
begin
  rw [nat.odd_iff_not_even, even_iff_two_dvd],
  rw nat.prime_dvd_prime_iff_eq nat.prime_two h,
  exact ne_of_lt hp
end

private lemma odd_pow_lem (a : ℤ) (n k : ℕ) (h₁ : k ∣ n) (h₂ : odd (n / k)) : a^k + 1 ∣ a^n + 1 :=
begin
  -- Let m be the natural number such that k * m = n. Then (-1)^m = -1 since m is odd by hypothesis.
  generalize h₃ : n / k = m,
  have hm : k * m = n := by { rw [←h₃, mul_comm], exact nat.div_mul_cancel h₁ },
  have hm₁ : (-1 : ℤ)^m = -1 := odd.neg_one_pow (h₃ ▸ h₂),

  -- a^k ≡ -1 (mod a^k + 1)
  have hk : a^k + 1 ∣ a^k + 1 - 1 -(-1) := by norm_num,
  have hk₁ : a^k + 1 - 1 ≡ -1 [ZMOD a^k + 1] := (int.modeq_of_dvd hk).symm,
  have hk₂ : a^k ≡ -1 [ZMOD a^k + 1] := by rwa int.add_sub_cancel at hk₁,

  -- a^n = (a^k)^m ≡ (-1)^m = -1 (mod a^k + 1)
  have ha : a^n = (a^k)^m := by rw [←pow_mul, hm],
  have ha₂ : (a^k)^m ≡ (-1)^m [ZMOD a^k + 1] := int.modeq.pow m hk₂,
  have ha₃ : a^n ≡ (-1)^m [ZMOD a^k + 1] := (eq.symm ha) ▸ ha₂,
  have ha₄ : a^n ≡ (-1) [ZMOD a^k + 1] := hm₁ ▸ ha₃,

  -- Therefore, a^k + 1 divides a^n + 1
  show a^k + 1 ∣ a^n + 1, from (int.modeq.symm ha₄).dvd
end

private lemma sub_one_dvd_pow_sub_one (a n : ℕ) (h : a ≥ 1) : a - 1 ∣ a^n - 1 :=
begin
  induction n with n ih,
  { simp },
  { have h₁ : a - 1 ∣ a * (a^n - 1) := dvd_mul_of_dvd_right ih _,
    have h₂ : 0 < a := by linarith,
    have h₃ : 1 ≤ a ^ n := nat.one_le_pow n a h₂,
    have : a ≤ a * a ^ n := (le_mul_iff_one_le_right h₂).mpr h₃,
    rw calc a ^ (n.succ) - 1 = a ^ (n + 1) - 1 : rfl
                         ... = a * a ^ n - 1 : by rw pow_succ
                         ... = a * a ^ n - a + a - 1 : by rw nat.sub_add_cancel this
                         ... = a * a ^ n - a * 1 + a - 1 : by simp
                         ... = a * (a ^ n - 1) + a - 1 : by rw nat.mul_sub_left_distrib
                         ... = a * (a ^ n - 1) + (a - 1) : by rw nat.add_sub_assoc h,
    exact dvd_add h₁ (dvd_refl _),
  }
end

private lemma pow_gt_base (a b : ℕ) (ha : 1 < a) (hb : 1 < b) : a < a^b :=
begin
  have ha₁ : 0 < a := pos_of_gt ha,
  have hb₁ : 1 ≤ b := le_of_lt hb,

  rw [←nat.sub_add_cancel hb₁, pow_succ a (b - 1)],
  nth_rewrite_lhs 0 ←mul_one a,
  suffices h : 1 < (a^(b - 1)),
  { exact mul_lt_mul_of_pos_left h ha₁ },
  have : 0 < (b - 1) := tsub_pos_of_lt hb,
  exact (b - 1).one_lt_pow a this ha
end

private lemma pow_gt_exponent (a b : ℕ) (h : 2 ≤ a) : b < a^b :=
begin
  induction b with b hb,
  { rw pow_zero,
    norm_num },
  { have q : 1 ≤ b.succ := nat.succ_le_succ (zero_le b),
    have q₁ : 1 ≤ a := nat.le_of_succ_le h,
    have q₂ : 0 < (a - 1)*(b + 1) := begin
      have : 1 ≤ a - 1 := (le_tsub_iff_left q₁).mpr h,
      have hpos₁ : 0 < a - 1 := nat.succ_le_iff.mp this,
      have hpos₂ : 0 < b + 1 := nat.succ_pos b,
      exact mul_pos hpos₁ hpos₂
    end,
    have hb₁ : b + 1 ≤ a ^ b := nat.succ_le_iff.mpr hb,
    rw pow_succ,
    calc a * a ^ b ≥ a * (b + 1)               : mul_le_mul_left' hb₁ a
               ... = (a - 1 + 1)*(b + 1)       : by rwa nat.sub_add_cancel q₁
               ... = (a - 1)*(b + 1) + (b + 1) : by rw [add_mul, one_mul]
               ... > b + 1                     : by linarith }
end

private lemma a_id_helper (a b : ℕ) (ha : 1 < a) (hb : 1 < b) : 1 < (a^b - 1)/(a - 1) :=
begin
  have ha₁ : 1 ≤ a := by linarith,

  -- It suffices to show that a - 1 < a^b - 1
  suffices h : 1*(a - 1) < (a^b - 1)/(a - 1)*(a - 1),
  { exact lt_of_mul_lt_mul_right' h },
  have h₁ : a - 1 ∣ a^b - 1 := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ a, by linarith),
  rw nat.div_mul_cancel h₁,
  rw one_mul,

  -- Since a < a^b, a - 1 ≤ a^b - 1
  have h₂ : a < a^b := pow_gt_base a b ha hb,
  show a - 1 < a^b - 1, from (tsub_lt_tsub_iff_right ha₁).mpr h₂,
end

private lemma b_id_helper (a b : ℕ) (ha : 1 < a) (hb : 2 < b) : 1 < (a^b + 1)/(a + 1) :=
begin
  have ha₁ : 2 ≤ a := nat.succ_le_iff.mpr ha,
  have hb₁ : 1 ≤ b := nat.one_le_of_lt hb,

  -- To show that 1 < (a^b + 1) / (a + 1), we only need to show that 2*a + 2 ≤ (a^b + 1)
  suffices h : 2 ≤ (a^b + 1) / (a + 1),
  { exact nat.succ_le_iff.mp h },
  suffices h : 2*(a + 1) ≤ (a ^ b + 1),
  { have h₁ : 2*(a + 1)/(a + 1) ≤ (a ^ b + 1)/(a + 1) := nat.div_le_div_right h,
    have h₂ : 0 < a + 1 := nat.succ_pos a,
    rwa nat.mul_div_cancel _ h₂ at h₁ },
  rw [mul_add, mul_one],

  -- Because 2 ≤ a and 2 < b, 3 ≤ a^(b - 1)
  have h₁ : 3 ≤ a^(b - 1),
  { have : 2 ≤ b - 1 := nat.le_pred_of_lt hb,
    calc a^(b - 1) ≥ a^2 : (pow_le_pow_iff ha).mpr this
               ... ≥ 2^2 : pow_le_pow_of_le_left' ha₁ 2
               ... ≥ 3   : by norm_num },

  -- Since we know that 3 ≤ a ^ (b - 1), if we want to show 2 * a + 1 ≤ a ^ b then it suffices to
  -- show that 2 * a + 1 ≤ 3 * a because then 2 * a + 1 ≤ a * 3 ≤ a * a^(b - 1) = a ^ b
  rw [←nat.sub_add_cancel hb₁, pow_succ],
  suffices h : 2 * a + 1 ≤ a * a^(b - 1),
  { exact nat.succ_le_succ h },
  suffices h : 2 * a + 1 ≤ a * 3,
  { exact le_mul_of_le_mul_left h h₁ },
  rw mul_comm a 3,

  -- Because 1 ≤ a, a + 1 ≤ 3 * a
  have : 3 * a = 2 * a + a := add_one_mul 2 a,
  rw this,
  have h : 1 ≤ a := le_of_lt ha,
  exact add_le_add_left h (2 * a)
end

private lemma AB_id_helper (b p : ℕ) (hb : 2 ≤ b) (hp : odd p)
  : ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) = ((b ^ (2*p)) - 1) / (b^2 - 1) :=
have q₁ : (b - 1) ∣ (b ^ p - 1) := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ b, by linarith),
have q₂ : (b + 1) ∣ (b ^ p + 1) := begin
  have : odd (p / 1) := eq.symm (nat.div_one p) ▸ hp,
  have h := odd_pow_lem ↑b p 1 (one_dvd p) this,
  rw pow_one at h,
  exact_mod_cast h,
end,
have q₃ : 1 ≤ (b^p) := nat.one_le_pow p b (show 0 < b, by linarith),
calc ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) = ((b ^ p - 1) * (b ^ p + 1)) / ((b - 1) * (b + 1)) : nat.div_mul_div_comm q₁ q₂
  ... = ((b ^ p + 1) * (b ^ p - 1)) / ((b - 1) * (b + 1)) : by rw mul_comm
  ... = ((b ^ p)^2 - 1^2) / ((b - 1) * (b + 1))           : by rw nat.sq_sub_sq
  ... = ((b ^ (p*2)) - 1^2) / ((b - 1) * (b + 1))         : by rw pow_mul
  ... = ((b ^ (2*p)) - 1^2) / ((b - 1) * (b + 1))         : by rw mul_comm
  ... = ((b ^ (2*p)) - 1^2) / ((b + 1) * (b - 1))         : by rw mul_comm (b + 1)
  ... = ((b ^ (2*p)) - 1^2) / (b^2 - 1^2)                 : by rw nat.sq_sub_sq
  ... = ((b ^ (2*p)) - 1) / (b^2 - 1)                     : by rw one_pow

/--
Given a prime `p` which does not divide `b*(b^2 - 1)`, we can produce a number `n` which is larger
than `p` and pseudoprime to base `b`. We do this by defining
`n = ((b^p - 1)/(b - 1)) * ((b^p + 1)/(b + 1))`

The primary purpose of this definition is to help prove `exists_infinite_pseudoprimes`. For a proof
that `n` is actually pseudoprime to base `b`, see `psp_from_prime_psp`, and for a proof that `n` is
greater than `p`, see `psp_from_prime_gt_p`.
-/
private def psp_from_prime (b : ℕ) (b_ge_two : 2 ≤ b) (p : ℕ) (p_prime : nat.prime p)
  (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b*(b^2 - 1)) : ℕ :=
have A : ℕ := (b^p - 1)/(b - 1),
have B : ℕ := (b^p + 1)/(b + 1),
A * B

/--
This is a proof that the number produced using `psp_from_prime` is actually pseudoprime to base `b`.
The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.

We use <https://primes.utm.edu/notes/proofs/a_pseudoprimes.html> as a rough outline of the proof.
-/
private lemma psp_from_prime_psp (b : ℕ) (b_ge_two : 2 ≤ b) (p : ℕ) (p_prime : nat.prime p)
  (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  fermat_psp (psp_from_prime b b_ge_two p p_prime p_gt_two not_dvd) b :=
begin
  unfold psp_from_prime,
  generalize A_id : (b^p - 1)/(b - 1) = A,
  generalize B_id : (b^p + 1)/(b + 1) = B,

  -- Inequalities
  have hi_A : 1 < A,
  { rw ←A_id,
    refine a_id_helper b p _ _,
    { exact nat.succ_le_iff.mp b_ge_two },
    { exact nat.prime.one_lt p_prime } },
  have hi_B : 1 < B,
  { rw ←B_id,
    refine b_id_helper b p _ p_gt_two,
    { exact nat.succ_le_iff.mp b_ge_two } },
  have hi_AB : 1 < (A * B) := one_lt_mul'' hi_A hi_B,
  have hi_b : 0 < b := by linarith,
  have hi_p : 1 ≤ p := nat.one_le_of_lt p_gt_two,
  have hi_bsquared : 1 ≤ (b^2) := nat.one_le_pow _ _ hi_b,
  have hi_bpowtwop : 1 ≤ (b^(2*p)) := nat.one_le_pow (2*p) b hi_b,
  have hi_bpowp_ge_b : (b ≤ b^p),
  { have : 1 ≤ b^(p - 1) := (p - 1).one_le_pow b hi_b,
    calc b^p = b*b^(p - 1) : nat.sub_add_cancel hi_p ▸ pow_succ b (p - 1)
         ... ≥ b*1         : mul_le_mul_left' this b
         ... = b           : by rw mul_one },
  have hi_bsquared₁ : 0 < (b^2 - 1) := by nlinarith,
  have hi_bpowpsubone : 1 ≤ b ^ (p - 1) := nat.one_le_pow (p - 1) b hi_b,

  -- Other useful facts
  have p_odd : odd p := odd_of_prime_gt_two p p_prime p_gt_two,
  have AB_not_prime : ¬(nat.prime (A * B)) := nat.not_prime_mul hi_A hi_B,
  have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1),
  { rw ←A_id,
    rw ←B_id,
    exact AB_id_helper _ _ b_ge_two p_odd },
  have hd : (b^2 - 1) ∣ (b^(2*p) - 1),
  { have : b^2 - 1 ∣ (b ^ 2) ^ p - 1 := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ b ^ 2, by linarith),
    rwa ←pow_mul at this },

  have AB_probable_prime : probable_prime (A * B) b, {
    unfold probable_prime,

    -- Rewrite AB_id. Used to prove that `2*p*(b^2 - 1) ∣ (b^2 - 1)*(A*B - 1)`.
    have ha₁ : (b^2 - 1) * ((A*B) - 1) = b*(b^(p-1) - 1)*(b^p + b), {
      apply_fun (λx, x*(b^2 - 1)) at AB_id,
      rw nat.div_mul_cancel hd at AB_id,
      apply_fun (λx, x - (b^2 - 1)) at AB_id,
      nth_rewrite 1 ←one_mul (b^2 - 1) at AB_id,
      rw [←nat.mul_sub_right_distrib, mul_comm] at AB_id,
      calc (b^2 - 1) * (A * B - 1) = b ^ (2 * p) - 1 - (b^2 - 1) : AB_id
        ... = b ^ (2 * p) - (1 + (b^2 - 1))           : by rw nat.sub_sub
        ... = b ^ (2 * p) - (1 + b^2 - 1)             : by rw nat.add_sub_assoc hi_bsquared
        ... = b ^ (2 * p) - (b^2)                     : by rw nat.add_sub_cancel_left
        ... = b ^ (p * 2) - (b^2)                     : by rw mul_comm
        ... = (b ^ p) ^ 2 - (b^2)                     : by rw pow_mul
        ... = (b ^ p + b) * (b ^ p - b)               : by rw nat.sq_sub_sq
        ... = (b ^ p - b) * (b ^ p + b)               : by rw mul_comm
        ... = (b ^ (p - 1 + 1) - b) * (b ^ p + b)     : by rw nat.sub_add_cancel hi_p
        ... = (b * b ^ (p - 1) - b) * (b ^ p + b)     : by rw pow_succ
        ... = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) : by rw mul_one
        ... = b * (b ^ (p - 1) - 1) * (b ^ p + b)     : by rw nat.mul_sub_left_distrib
    },
    -- If `b` is even, then `b^p` is also even, so `2 ∣ b^p + b`
    -- If `b` is odd, then `b^p` is also odd, so `2 ∣ b^p + b`
    have ha₂ : 2 ∣ b^p + b,
    { apply @decidable.by_cases (even b),
      { intro h,
        replace h : 2 ∣ b := even_iff_two_dvd.mp h,
        have : p ≠ 0 := by linarith,
        have : 2 ∣ b^p := dvd_pow h this,
        exact dvd_add this h },
      { intro h,
        have h : odd b := nat.odd_iff_not_even.mpr h,
        have : prime 2 := nat.prime_iff.mp (by norm_num),
        have : odd (b^p) := odd.pow h,
        have : even ((b^p) + b) := odd.add_odd this h,
        exact even_iff_two_dvd.mp this } },
    -- Since b isn't divisible by p, we can use Fermat's Little Theorem to prove this
    have ha₃ : p ∣ (b^(p - 1) - 1),
    { have : ¬p ∣ b := mt (assume h : p ∣ b, dvd_mul_of_dvd_left h _) not_dvd,
      have : (b : zmod p) ≠ 0 := assume h, absurd ((zmod.nat_coe_zmod_eq_zero_iff_dvd b p).mp h) this,
      -- by Fermat's Little Theorem, b^(p - 1) ≡ 1 (mod p)
      have q := @zmod.pow_card_sub_one_eq_one _ (fact.mk p_prime) (↑b) this,
      apply_fun (λ x, x - 1) at q,
      rw sub_self at q,
      apply (zmod.nat_coe_zmod_eq_zero_iff_dvd (b^(p - 1) - 1) p).mp,
      have : 1 ≤ b ^ (p - 1) := hi_bpowpsubone, -- needed for norm_cast
      norm_cast at q,
      exact q },
    -- This follows from the fact that `p - 1` is even
    have ha₄ : ((b^2) - 1) ∣ (b^(p - 1) - 1),
    { unfold odd at p_odd,
      cases p_odd with k hk,
      have : 2 ∣ p - 1,
      { rw hk,
        rw nat.add_sub_cancel,
        exact dvd.intro k rfl },
      unfold has_dvd.dvd at this,
      cases this with c hc,
      have : ((b^2) - 1) ∣ ((b^2)^c - 1) := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ b ^ 2, by linarith),
      have : ((b^2) - 1) ∣ (b^(2*c) - 1) := by rwa ←pow_mul at this,
      rwa ← hc at this },
    -- Used to prove that `2*p` divides `A*B - 1`
    have ha₅ : 2*p*(b^2 - 1) ∣ (b^2 - 1)*(A*B - 1),
    { suffices q : 2*p*(b^2 - 1) ∣ b*(b^(p-1) - 1)*(b^p + b),
      { rwa ha₁ },
      -- We already proved that `b^2 - 1 ∣ b^(p - 1) - 1`.
      -- Since `2 ∣ b^p + b` and `p ∣ b^p + b`, if we show that 2 and p are coprime, then we
      -- know that `2 * p ∣ b^p + b`
      have q₁ : nat.coprime p (b^2 - 1),
      { have q₂ : ¬p ∣ (b^2 - 1),
        { rw mul_comm at not_dvd,
          exact mt (assume h : p ∣ b ^ 2 - 1, dvd_mul_of_dvd_left h _) not_dvd },
        exact (nat.prime.coprime_iff_not_dvd p_prime).mpr q₂ },
      have q₂ : p*(b^2 - 1) ∣ b^(p - 1) - 1 := nat.coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄,
      have q₃ : p*(b^2 - 1)*2 ∣ (b^(p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂,
      have q₄ : p*(b^2 - 1)*2 ∣ b * ((b^(p - 1) - 1) * (b ^ p + b)) := dvd_mul_of_dvd_right q₃ _,
      rwa [mul_assoc, mul_comm, mul_assoc b] },
    have ha₆ : 2*p ∣ A*B - 1,
    { rw mul_comm at ha₅,
      exact nat.dvd_of_mul_dvd_mul_left hi_bsquared₁ ha₅ },
    -- Multiply both sides of `AB_id` by `a^2 - 1` then add 1
    have ha₇ : b^(2*p) = 1 + A*B*(b^2 - 1),
    { have q : A*B * (b^2-1) = (b^(2*p)-1)/(b^2-1)*(b^2-1) := congr_arg (λx : ℕ, x * (b^2 - 1)) AB_id,
      rw nat.div_mul_cancel hd at q,
      apply_fun (λ x : ℕ, x + 1) at q,
      rw nat.sub_add_cancel hi_bpowtwop at q,
      rw add_comm at q,
      exact q.symm },
    have ha₈ : A*B ∣ b^(2*p) - 1,
    { unfold has_dvd.dvd,
      use (b^2 - 1),
      exact norm_num.sub_nat_pos (b ^ (2 * p)) 1 (A * B * (b ^ 2 - 1)) (eq.symm ha₇) },
    -- Since `2*p ∣ A*B - 1`, there is a number (which we call `q`) such that `2*p*q = A*B - 1`.
    -- Since `2*p*q` is divisible by `2*p`, we know that `b^(2*p) - 1 ∣ b^(2*p*q) - 1`.
    -- This means that `b^(2*p) - 1 ∣ b^(A*B - 1) - 1`.
    -- We already proved that `A*B ∣ b^(2*p) - 1`, implying that `A*B ∣ b^(A*B - 1) - 1`
    generalize ha₉ : (A*B - 1) / (2*p) = q,
    have ha₁₀ : q * (2*p) = (A*B - 1) := by rw [←ha₉, nat.div_mul_cancel ha₆],
    have ha₁₁ : b^(2*p) - 1 ∣ (b^(2*p))^q - 1 := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ b^(2*p), by linarith),
    rw ← pow_mul at ha₁₁,
    rw mul_comm (2*p) at ha₁₁,
    rw ha₁₀ at ha₁₁,
    exact dvd_trans ha₈ ha₁₁
  },
  exact ⟨AB_probable_prime, AB_not_prime, hi_AB⟩
end

/--
This is a proof that the number produced using `psp_from_prime` is greater than the prime `p` used
to create it. The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.
-/
private lemma psp_from_prime_gt_p (b : ℕ) (b_ge_two : 2 ≤ b) (p : ℕ) (p_prime : nat.prime p)
  (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  p < psp_from_prime b b_ge_two p p_prime p_gt_two not_dvd :=
begin
  unfold psp_from_prime,
  generalize A_id : (b^p - 1)/(b - 1) = A,
  generalize B_id : (b^p + 1)/(b + 1) = B,
  have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1),
  { rw ←A_id,
    rw ←B_id,
    have p_odd : odd p := odd_of_prime_gt_two p p_prime p_gt_two,
    exact AB_id_helper _ _ b_ge_two p_odd },
  have AB_dvd : (b^2 - 1) ∣ (b^(2*p) - 1),
  { have : b^2 - 1 ∣ (b ^ 2) ^ p - 1 := sub_one_dvd_pow_sub_one _ _ (show 1 ≤ b ^ 2, by nlinarith),
    rwa ←pow_mul at this },
  rw AB_id,
  suffices h : p * (b ^ 2 - 1) < b ^ (2 * p) - 1,
  { have h₁ : (p * (b ^ 2 - 1)) / (b ^ 2 - 1) < (b ^ (2 * p) - 1) / (b ^ 2 - 1),
    { exact nat.div_lt_div_of_lt_of_dvd AB_dvd h },
    have h₂ : 0 < b ^ 2 - 1,
    { have : 4 ≤ b ^ 2 := by nlinarith,
      have : 3 ≤ b ^ 2 - 1 := le_tsub_of_add_le_left this,
      linarith },
    rwa nat.mul_div_cancel _ h₂ at h₁ },
  rw [nat.mul_sub_left_distrib, mul_one],
  rw pow_mul,
  nth_rewrite_rhs 0 ←nat.sub_add_cancel (show 1 ≤ p, by linarith),
  rw pow_succ (b ^ 2),
  suffices h : p * b ^ 2 < b ^ 2 * (b ^ 2) ^ (p - 1),
  { apply gt_of_ge_of_gt,
    { exact tsub_le_tsub_left (show 1 ≤ p, by linarith) (b ^ 2 * (b ^ 2) ^ (p - 1)) },
    { have : p ≤ p * b ^ 2 := nat.le_mul_of_pos_right (show 0 < b ^ 2, by nlinarith),
      exact tsub_lt_tsub_right_of_le this h } },

  suffices h : p < (b ^ 2) ^ (p - 1),
  { rw mul_comm (b ^ 2),
    have : 4 ≤ b^2 := by nlinarith,
    have : 0 < b^2 := by linarith,
    exact mul_lt_mul_of_pos_right h this },

  rw ←pow_mul,
  rw nat.mul_sub_left_distrib,
  rw mul_one,

  have h₁ : 2 ≤ 2*p - 2,
  { have q : 4 ≤ 2*p := by linarith,
    exact le_tsub_of_add_le_left q },

  have : 2 + p ≤ 2 * p := by linarith,
  have : p ≤ 2 * p - 2 := le_tsub_of_add_le_left this,
  have q : (2*p - 2) < b^(2*p - 2) := pow_gt_exponent _ _ b_ge_two,

  exact nat.lt_of_le_of_lt this q
end

/--
For all positive bases, there exist Fermat infinite pseudoprimes to that base.
Given in this form: for all numbers `b ≥ 1` and `m`, there exists a pseudoprime `n` to base `b` such
that `m ≤ n`. This form is similar to `nat.exists_infinite_primes`.
-/
theorem exists_infinite_pseudoprimes (b : ℕ) (h : 1 ≤ b) (m : ℕ) : ∃ n : ℕ, fermat_psp n b ∧ m ≤ n
:=
begin
  by_cases b_ge_two : 2 ≤ b,
  -- If `2 ≤ b`, then because there exist infinite prime numbers, there is a prime number p such
  -- `m ≤ p` and `¬p ∣ b*(b^2 - 1)`. We pick a prime number `b*(b^2 - 1) + 1 + m ≤ p` because we
  -- automatically know that p is greater than m and that it does not divide `b*(b^2 - 1)`
  -- (because p can't divide a number less than p).
  -- From p, we can use the lemmas we proved earlier to show that
  -- `((b^p - 1)/(b - 1)) * ((b^p + 1)/(b + 1))` is a pseudoprime to base b.
  { have h := nat.exists_infinite_primes ((b*(b^2 - 1)) + 1 + m),
    cases h with p hp,
    cases hp with hp₁ hp₂,
    have h₁ : 0 < b := pos_of_gt (nat.succ_le_iff.mp b_ge_two),
    have h₂ : 4 ≤ b^2 := pow_le_pow_of_le_left' b_ge_two 2,
    have h₃ : 0 < (b^2 - 1) := tsub_pos_of_lt (gt_of_ge_of_gt h₂ (by norm_num)),
    have h₄ : 0 < (b*(b^2 - 1)) := mul_pos h₁ h₃,
    have h₁ : (b*(b^2 - 1)) < p := by linarith,
    have h₂ : ¬p ∣ (b*(b^2 - 1)) := nat.not_dvd_of_pos_of_lt h₄ h₁,
    have h₅ : b ≤ b*(b^2 - 1) := nat.le_mul_of_pos_right h₃,
    have h₆ : 2 ≤ b*(b^2 - 1) := le_trans b_ge_two h₅,
    have h₇ : 2 < p := gt_of_gt_of_ge h₁ h₆,
    have h₈ := psp_from_prime_gt_p b b_ge_two p hp₂ h₇ h₂,
    use psp_from_prime b b_ge_two p hp₂ h₇ h₂,
    split,
    { exact psp_from_prime_psp b b_ge_two p hp₂ h₇ h₂ },
    { exact le_trans (show m ≤ p, by linarith) (le_of_lt h₈) } },
  -- If `¬2 ≤ b`, then `b = 1`. Since all composite numbers are pseudoprimes to base 1, we can pick
  -- any composite number greater than m. We choose 2 * (m + 2) because it is greater than m and is
  -- composite for all natural numbers m.
  { have h₁ : b = 1 := by linarith,
    rw h₁,
    use 2 * (m + 2),
    have : ¬nat.prime (2 * (m + 2)) := nat.not_prime_mul (by norm_num) (by norm_num),
    exact ⟨pseudoprime_of_base_one _ (by linarith) this, by linarith⟩ }
end

end fermat_psp
