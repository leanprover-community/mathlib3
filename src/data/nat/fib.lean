/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import data.nat.gcd
import logic.function.iterate
import data.finset.nat_antidiagonal
import algebra.big_operators.basic
import tactic.ring
import tactic.zify

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `nat.fib` returns the stream of Fibonacci numbers.

## Main Statements

- `nat.fib_add_two`: shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `nat.fib_gcd`: `fib n` is a strong divisibility sequence.
- `nat.fib_succ_eq_sum_choose`: `fib` is given by the sum of `nat.choose` along an antidiagonal.
- `nat.fib_succ_eq_succ_sum`: shows that `F₀ + F₁ + ⋯ + Fₙ = Fₙ₊₂ - 1`.
- `nat.fib_two_mul` and `nat.fib_two_mul_add_one` are the basis for an efficient algorithm to
  compute `fib` (see `nat.fast_fib`). There are `bit0`/`bit1` variants of these can be used to
  simplify `fib` expressions: `simp only [nat.fib_bit0, nat.fib_bit1, nat.fib_bit0_succ,
  nat.fib_bit1_succ, nat.fib_one, nat.fib_two]`.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/

open_locale big_operators

namespace nat

/--
Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
@[pp_nodot]
def fib (n : ℕ) : ℕ := ((λ p : ℕ × ℕ, (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

@[simp] lemma fib_zero : fib 0 = 0 := rfl
@[simp] lemma fib_one : fib 1 = 1 := rfl
@[simp] lemma fib_two : fib 2 = 1 := rfl

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
lemma fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) :=
by simp only [fib, function.iterate_succ']

lemma fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by { cases n; simp [fib_add_two] }

@[mono] lemma fib_mono : monotone fib :=
monotone_nat_of_le_succ $ λ _, fib_le_fib_succ

lemma fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n :=
calc 0 < fib 1 : dec_trivial
   ... ≤ fib n : fib_mono n_pos

lemma fib_add_two_sub_fib_add_one {n : ℕ} : fib (n + 2) - fib (n + 1) = fib n :=
by rw [fib_add_two, add_tsub_cancel_right]

lemma fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) :=
begin
  rcases le_iff_exists_add.1 hn with ⟨n, rfl⟩,
  rw [← tsub_pos_iff_lt, add_comm 2, fib_add_two_sub_fib_add_one],
  apply fib_pos (succ_pos n),
end

/-- `fib (n + 2)` is strictly monotone. -/
lemma fib_add_two_strict_mono : strict_mono (λ n, fib (n + 2)) :=
begin
  refine strict_mono_nat_of_lt_succ (λ n, _),
  rw add_right_comm,
  exact fib_lt_fib_succ (self_le_add_left _ _)
end

lemma le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n :=
begin
  induction five_le_n with n five_le_n IH,
  { -- 5 ≤ fib 5
    refl },
  { -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw succ_le_iff,
    calc n ≤ fib n       : IH
       ... < fib (n + 1) : fib_lt_fib_succ (le_trans dec_trivial five_le_n) }
end

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
lemma fib_coprime_fib_succ (n : ℕ) : nat.coprime (fib n) (fib (n + 1)) :=
begin
  induction n with n ih,
  { simp },
  { rw [fib_add_two, coprime_add_self_right],
    exact ih.symm }
end

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
lemma fib_add (m n : ℕ) :
  fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) :=
begin
  induction n with n ih generalizing m,
  { simp },
  { intros,
    specialize ih (m + 1),
    rw [add_assoc m 1 n, add_comm 1 n] at ih,
    simp only [fib_add_two, ih],
    ring, }
end

lemma fib_two_mul (n : ℕ) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) :=
begin
  cases n,
  { simp },
  { rw [nat.succ_eq_add_one, two_mul, ←add_assoc, fib_add, fib_add_two, two_mul],
    simp only [← add_assoc, add_tsub_cancel_right],
    ring, },
end

lemma fib_two_mul_add_one (n : ℕ) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 :=
by { rw [two_mul, fib_add], ring }

lemma fib_bit0 (n : ℕ) : fib (bit0 n) = fib n * (2 * fib (n + 1) - fib n) :=
by rw [bit0_eq_two_mul, fib_two_mul]

lemma fib_bit1 (n : ℕ) : fib (bit1 n) = fib (n + 1) ^ 2 + fib n ^ 2 :=
by rw [nat.bit1_eq_succ_bit0, bit0_eq_two_mul, fib_two_mul_add_one]

lemma fib_bit0_succ (n : ℕ) : fib (bit0 n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := fib_bit1 n

lemma fib_bit1_succ (n : ℕ) : fib (bit1 n + 1) = fib (n + 1) * (2 * fib n + fib (n + 1)) :=
begin
  rw [nat.bit1_eq_succ_bit0, fib_add_two, fib_bit0, fib_bit0_succ],
  have : fib n ≤ 2 * fib (n + 1),
  { rw two_mul,
    exact le_add_left fib_le_fib_succ, },
  zify,
  ring,
end

/-- Computes `(nat.fib n, nat.fib (n + 1))` using the binary representation of `n`.
Supports `nat.fast_fib`. -/
def fast_fib_aux : ℕ → ℕ × ℕ :=
nat.binary_rec (fib 0, fib 1) (λ b n p,
  if b
  then (p.2^2 + p.1^2, p.2 * (2 * p.1 + p.2))
  else (p.1 * (2 * p.2 - p.1), p.2^2 + p.1^2))

/-- Computes `nat.fib n` using the binary representation of `n`.
Proved to be equal to `nat.fib` in `nat.fast_fib_eq`. -/
def fast_fib (n : ℕ) : ℕ := (fast_fib_aux n).1

lemma fast_fib_aux_bit_ff (n : ℕ) :
  fast_fib_aux (bit ff n) = let p := fast_fib_aux n in (p.1 * (2 * p.2 - p.1), p.2^2 + p.1^2) :=
begin
  rw [fast_fib_aux, binary_rec_eq],
  { refl },
  { simp },
end

lemma fast_fib_aux_bit_tt (n : ℕ) :
  fast_fib_aux (bit tt n) = let p := fast_fib_aux n in (p.2^2 + p.1^2, p.2 * (2 * p.1 + p.2)) :=
begin
  rw [fast_fib_aux, binary_rec_eq],
  { refl },
  { simp },
end

lemma fast_fib_aux_eq (n : ℕ) :
  fast_fib_aux n = (fib n, fib (n + 1)) :=
begin
  apply nat.binary_rec _ (λ b n' ih, _) n,
  { simp [fast_fib_aux] },
  { cases b; simp only [fast_fib_aux_bit_ff, fast_fib_aux_bit_tt,
      congr_arg prod.fst ih, congr_arg prod.snd ih, prod.mk.inj_iff]; split;
    simp [bit, fib_bit0, fib_bit1, fib_bit0_succ, fib_bit1_succ], },
end

lemma fast_fib_eq (n : ℕ) : fast_fib n = fib n :=
by rw [fast_fib, fast_fib_aux_eq]

lemma gcd_fib_add_self (m n : ℕ) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) :=
begin
  cases nat.eq_zero_or_pos n,
  { rw h, simp },
  replace h := nat.succ_pred_eq_of_pos h, rw [← h, succ_eq_add_one],
  calc gcd (fib m) (fib (n.pred + 1 + m))
        = gcd (fib m) (fib (n.pred) * (fib m) + fib (n.pred + 1) * fib (m + 1)) :
    by { rw ← fib_add n.pred _, ring_nf }
    ... = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) :
    by rw [add_comm, gcd_add_mul_right_right (fib m) _ (fib (n.pred))]
    ... = gcd (fib m) (fib (n.pred + 1)) :
    coprime.gcd_mul_right_cancel_right
      (fib (n.pred + 1)) (coprime.symm (fib_coprime_fib_succ m))
end

lemma gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)
| 0     := by simp
| (k+1) := by rw [← gcd_fib_add_mul_self k, add_mul, ← add_assoc, one_mul, gcd_fib_add_self _ _]

/-- `fib n` is a strong divisibility sequence,
  see https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
lemma fib_gcd (m n : ℕ) : fib (gcd m n) = gcd (fib m) (fib n) :=
begin
  wlog h : m ≤ n using [n m, m n],
  exact le_total m n,
  { apply gcd.induction m n,
    { simp },
    intros m n mpos h,
    rw ← gcd_rec m n at h,
    conv_rhs { rw ← mod_add_div' n m },
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _] },
  rwa [gcd_comm, gcd_comm (fib m)]
end

lemma fib_dvd (m n : ℕ) (h : m ∣ n) : fib m ∣ fib n :=
by rwa [gcd_eq_left_iff_dvd, ← fib_gcd, gcd_eq_left_iff_dvd.mp]

lemma fib_succ_eq_sum_choose :
  ∀ (n : ℕ), fib (n + 1) = ∑ p in finset.nat.antidiagonal n, choose p.1 p.2 :=
two_step_induction rfl rfl (λ n h1 h2, by
{ rw [fib_add_two, h1, h2, finset.nat.antidiagonal_succ_succ', finset.nat.antidiagonal_succ'],
  simp [choose_succ_succ, finset.sum_add_distrib, add_left_comm] })

lemma fib_succ_eq_succ_sum (n : ℕ):
  fib (n + 1) = (∑ k in finset.range n, fib k) + 1 :=
begin
  induction n with n ih,
  { simp },
  { calc fib (n + 2) = fib n + fib (n + 1)                        : fib_add_two
                 ... = fib n + (∑ k in finset.range n, fib k) + 1 : by rw [ih, add_assoc]
                 ... = (∑ k in finset.range (n + 1), fib k) + 1   : by simp [finset.range_add_one] }
end

end nat
