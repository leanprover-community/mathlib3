/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import data.nat.gcd
import logic.function.iterate
import tactic.ring

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `fib` returns the stream of Fibonacci numbers.

## Main Statements

- `fib_add_two` : shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `fib_gcd`     : `fib n` is a strong divisibility sequence.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/

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

lemma fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) :=
begin
  rcases le_iff_exists_add.1 hn with ⟨n, rfl⟩,
  simp only [add_comm 2, fib_add_two], rw add_comm,
  exact lt_add_of_pos_left _ (fib_pos succ_pos')
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
  fib m * fib n + fib (m + 1) * fib (n + 1) = fib (m + n + 1) :=
begin
  induction n with n ih generalizing m,
  { simp },
  { intros,
    specialize ih (m + 1),
    rw [add_assoc m 1 n, add_comm 1 n] at ih,
    simp only [fib_add_two, ← ih],
    ring, }
end


lemma gcd_fib_add_self (m n : ℕ) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) :=
begin
  cases nat.eq_zero_or_pos n,
  { rw h, simp },
  replace h := nat.succ_pred_eq_of_pos h, rw [← h, succ_eq_add_one],
  calc gcd (fib m) (fib (n.pred + 1 + m))
        = gcd (fib m) (fib (n.pred) * (fib m) + fib (n.pred + 1) * fib (m + 1)) :
    by { rw fib_add n.pred _, ring_nf }
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

end nat
