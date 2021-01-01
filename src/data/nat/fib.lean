/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import data.stream.basic
import tactic
import data.nat.gcd
/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `fib` returns the stream of Fibonacci numbers.

## Main Statements

- `fib_succ_succ` : shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `gcd_fib_fib`   : `fib n` is a strong divisibility sequence.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/

namespace nat

/-- Auxiliary function used in the definition of `fib_aux_stream`. -/
private def fib_aux_step : (ℕ × ℕ) → (ℕ × ℕ) := λ p, ⟨p.snd, p.fst + p.snd⟩

/-- Auxiliary stream creating Fibonacci pairs `⟨Fₙ, Fₙ₊₁⟩`. -/
private def fib_aux_stream : stream (ℕ × ℕ) := stream.iterate fib_aux_step ⟨0, 1⟩

/--
Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
@[pp_nodot]
def fib (n : ℕ) : ℕ := (fib_aux_stream n).fst

@[simp] lemma fib_zero : fib 0 = 0 := rfl
@[simp] lemma fib_one : fib 1 = 1 := rfl
@[simp] lemma fib_two : fib 2 = 1 := rfl

private lemma fib_aux_stream_succ {n : ℕ} :
    fib_aux_stream (n + 1) = fib_aux_step (fib_aux_stream n) :=
begin
  change (stream.nth (n + 1) $ stream.iterate fib_aux_step ⟨0, 1⟩) =
      fib_aux_step (stream.nth n $ stream.iterate fib_aux_step ⟨0, 1⟩),
  rw [stream.nth_succ_iterate, stream.map_iterate, stream.nth_map]
end

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
lemma fib_succ_succ {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) :=
by simp only [fib, fib_aux_stream_succ, fib_aux_step]

lemma fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n :=
begin
  induction n with n IH,
  case nat.zero { norm_num at n_pos },
  case nat.succ
  { cases n,
    case nat.zero { simp [fib_succ_succ, zero_lt_one] },
    case nat.succ
    { have : 0 ≤ fib n, by simp,
      exact (lt_add_of_nonneg_of_lt this $ IH n.succ_pos) }}
end

lemma fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by { cases n; simp [fib_succ_succ] }

lemma fib_mono {n m : ℕ} (n_le_m : n ≤ m) : fib n ≤ fib m :=
by { induction n_le_m with m n_le_m IH, { refl }, { exact (le_trans IH fib_le_fib_succ) }}

lemma le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n :=
begin
  induction five_le_n with n five_le_n IH,
  { have : 5 = fib 5, by refl,  -- 5 ≤ fib 5
    exact le_of_eq this },
  { -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    cases n with n', -- rewrite n = succ n' to use fib.succ_succ
    { have : 5 = 0, from nat.le_zero_iff.elim_left five_le_n, contradiction },
    rw fib_succ_succ,
    suffices : 1 + (n' + 1) ≤ fib n' + fib (n' + 1), by rwa [nat.succ_eq_add_one, add_comm],
    have : n' ≠ 0, by { intro h, have : 5 ≤ 1, by rwa h at five_le_n, norm_num at this },
    have : 1 ≤ fib n', from nat.succ_le_of_lt (fib_pos $ zero_lt_iff_ne_zero.mpr this),
    mono }
end

/-- https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
lemma fib_succ_coprime (n : ℕ) : gcd (fib n) (fib (n + 1)) = 1 :=
begin
  induction n with n ih,
  { simp },
  { convert ih using 1,
    rw [fib_succ_succ, succ_eq_add_one, gcd_rec, add_mod_right, gcd_comm (fib n),
      gcd_rec (fib (n + 1))], }
end

/-- https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
lemma fib_add (m n : ℕ) :
  fib m * fib n + fib (m + 1) * fib (n + 1) = fib (m + n + 1) :=
begin
  induction n with n ih generalizing m,
  { simp },
  { intros,
    specialize ih (m + 1),
    rw [add_assoc m 1 n, add_comm 1 n] at ih,
    simp only [fib_succ_succ, ← ih],
    ring, }
end


lemma gcd_fib_add_self' (m n : ℕ) : gcd (fib m) (fib n) = gcd (fib m) (fib (n + m)) :=
begin
  cases eq_zero_or_pos n,
  { rw h, simp },
  replace h := nat.succ_pred_eq_of_pos h, rw [← h, succ_eq_add_one],
  calc (fib m).gcd (fib (n.pred + 1)) 
        = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) :
    begin
      have hcop := coprime.symm (fib_succ_coprime m),
      rwa [gcd_comm, gcd_comm (fib m) _, mul_comm _ (fib (m + 1)), coprime.gcd_mul_left_cancel]
    end
    ... = gcd (fib m) (fib (n.pred) * (fib m) + fib (n.pred + 1) * fib (m + 1)) :
    by rw [gcd_add_self (fib m) _ (fib (n.pred)), add_comm]
    ... = m.fib.gcd (n.pred + 1 + m).fib :
    begin rw ← eq.symm (fib_add n.pred _), ring end
    ... = m.fib.gcd (n.pred + 1 + m).fib : by ring,
end

lemma gcd_fib_add_self (m n k : ℕ) : gcd (fib m) (fib n) = gcd (fib m) (fib (n + k * m)) :=
begin
  induction k with k hk,
  { simp },
  { rw [hk, gcd_fib_add_self' _ _],
    ring, }
end

lemma gcd_fib_fib' (m' n' : ℕ) (hmn : m' ≤ n') : gcd (fib m') (fib n') = fib (gcd m' n') :=
begin
  apply gcd.induction m' n',
  { simp },
  { intros m n mpos h,
    rw ←gcd_rec m n at h,
    conv_lhs { rw ← mod_add_div n m },
    rw [mul_comm, ← gcd_fib_add_self m (n % m) (n / m), gcd_comm],
    exact h, }
end

/-- `fib n` is a strong divisibility sequence.
  https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
lemma gcd_fib_fib (m n : ℕ) : gcd (fib m) (fib n) = fib (gcd m n) :=
begin
  cases le_total m n with m_le_n n_le_m,
  { exact gcd_fib_fib' m n m_le_n },
  { rw [gcd_comm, gcd_comm m n],
    exact gcd_fib_fib' n m n_le_m }
end

end nat
