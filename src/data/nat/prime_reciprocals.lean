/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Vladimir Goryachev, Stepan Nesterov
-/
import data.nat.prime
import data.set.intervals.basic
import topology.algebra.infinite_sum

/-!
# Implementing James Clarkson's (1966) proof that the sum of the prime reciprocals diverges.

Clarkson, James A. (1966) On the series of prime reciprocals. Proc. Amer. Math.
Soc., 17: 541; MR 32, #5573.
 -/
open set
open_locale topological_space classical big_operators nnreal

variables {α β : Type*}
variables [add_comm_group α] [topological_space α] [topological_add_group α]

variables {f : ℕ → α} {a : α} (n : ℕ)


---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- These definitions edited from those by Vladimir Goryachev & Stepan Nesterov in
-- https://gist.github.com/SymmetryUnbroken/d2bee9459764681b8efbed9b3a6dd16f
---------------------------------------------------------------------------------------------------
def nextprime (n : ℕ) : ℕ := nat.find (nat.exists_infinite_primes n)

def nth_prime : ℕ → ℕ
| 0 := 2
| (n + 1) := nextprime ((nth_prime n).succ)

def firstprimes (n : ℕ) := {p : ℕ | ∃ k : ℕ, p = nth_prime k ∧ k ≤ n}

noncomputable def primerec : ℕ → ℝ := λ n, 1/(nth_prime n)
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- We will argue that if the series of reciprocal primes converges then
-- so does the series of reciprocals 1/n, giving a contradiction.

-- Step 1:
-- If the series of reciprocal primes converges then there is some `k : ℕ` such that
-- `sum_{n=k+1}^{∞} (1/p_n) < 1/2`

-- Proof by Vladimir Goryachev & Stepan Nesterov (with slight edits):
lemma tail_bounded_of_summable (H : summable primerec) :
  (∃ n : ℕ, ∑' (i : ℕ), primerec (i + n) < 1/2) :=
begin
  have H' := summable.has_sum H,
  have ha1 := has_sum.tendsto_sum_nat H',
  rw metric.tendsto_at_top at ha1,
  cases ha1 (1/2) (by linarith) with n hn,
  use n,
  specialize hn n (le_refl n),
  dsimp at hn,
  have H1 := sum_add_tsum_nat_add n H,
  dsimp at H1,
  rw real.dist_eq at hn,
  rw abs_lt at hn,
  linarith,
end


-- This follows from the more general statement that
-- if `f : ℕ → ℚ` converges then for any `v : ℚ` with `0 < |v|` there is some `k : ℕ` such that
-- `sum_{n=k+1}^{∞} f < v`

-- (We can probably generalise this further from `ℚ`, but this suffices for now).

-- Modified from above proof
-- example {f : ℕ → ℚ} (hf : summable f) (v : ℚ) (hv : 0 < v) :
--     ∃ k : ℕ, tsum (λ i, f (i + k)) < v :=
-- begin
--   have H' := summable.has_sum hf,
--   have ha1 := has_sum.tendsto_sum_nat H',
--   rw metric.tendsto_at_top at ha1,
--   have : (v:ℝ) > 0, { simp only [gt_iff_lt], exact rat.cast_pos.mpr hv },
--   cases ha1 ↑v this with n hn,
--   use n,
--   specialize hn n (le_refl n),
--   dsimp at hn,
--   have H1 := sum_add_tsum_nat_add n hf,
--   dsimp at H1,
--   rw rat.dist_eq at hn,
--   rw abs_lt at hn,
--   linarith,
-- end


example : ¬ summable primerec :=
begin
-- Assume for contradition that the sequence `n ↦ 1/p_n` is summable.
  intros H,
-- Extract `k : ℕ` from the above lemma.
  cases tail_bounded_of_summable H with k hk,
-- Let `J := sum_{n=k+1}^{∞} (1/p_n) < 1/2`.
-- Let `Q := p_1 * ... p_k` be the product of the first k primes.

  sorry,
end

-- Step 3:
-- For any `t : ℕ`, the series `sum_{n=1}^{∞} J^t` is dominated by `sum_{n=1}^{∞} (1/2)^t`
-- and therefore converges.

-- Step 4:
-- For any `n`, `1 / (1 + n * Q)` is one of the summands in `sum_{n=1}^{∞} J^t`,
-- and hence there is an injective function to which we can apply `summable.comp_injective`.
-- To show this note that `1 + n*Q` is not divisible by any of the first `k` primes,
-- so all of its prime factors are greater than `p_k`.
-- EXPLAIN MORE HERE!

-- Step 5:
-- Since `sum_{n=1}^{∞} J^t` converges, and `sum_{n=1}^{∞} 1 / (1 + n * Q)` is
-- the sum of a subset of the terms of that series, this also converges.

-- Step 6:
-- For any K : ℕ we have
-- `sum_{n=1}^{∞} 1 / (1 + n * K) > sum_{n=1}^{∞} 1 / (n * K) = 1/K * sum_{n=1}^{∞} 1/n`

-- Step 7:
-- Hence, if `n ↦ 1/p_n` is summable then so is  `n ↦ 1/n`.  Contradiction.




/-- The infinite sum of `f` can be split into an initial finite sum plus the sum of the tail -/
example {f : ℕ → ℚ} {a : ℚ} (hf: summable f) (n : ℕ) :
  ∑' i, f i = (finset.range n).sum f + ∑' i, f (i + n) :=
(sum_add_tsum_nat_add n hf).symm



example {f g : ℕ → ℚ} (hfg : ∀ n : ℕ, f n ≤ g n) (hg : summable g) : summable f :=
begin

  sorry,
end





-- By the above,
-- `sum_{n=1}^{∞} 1 / (1 + n * Q)` diverges.
