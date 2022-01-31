/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
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

/-- The infinite sum of `f` can be split into an initial finite sum plus the sum of the tail -/
example {f : ℕ → ℚ} {a : ℚ} (hf: summable f) (n : ℕ) :
  ∑' i, f i = (finset.range n).sum f + ∑' i, f (i + n) :=
(sum_add_tsum_nat_add n hf).symm



-- If the series of reciprocal primes converges then there is some `k : ℕ` such that
-- `sum_{n=k+1}^{∞} (1/p_n) < 1/2`

-- This follows from the more general statement that
-- if `f : ℕ → ℚ` converges then for any `v : ℚ` with `0 < |v|` there is some `k : ℕ` such that
-- `sum_{n=k+1}^{∞} f < v`

-- (We can probably generalise this further from `ℚ`, but this suffices for now).

example {f : ℕ → ℚ} {a : ℚ} (hf : has_sum f a) (v : ℚ) (hv : 0 < v):
  ∃ k : ℕ, tsum (λ i, f (i + k)) < v := sorry
