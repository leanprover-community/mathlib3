/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import data.nat.parity
import algebra.big_operators.intervals
import tactic.ring
import data.real.basic

open finset set
open_locale big_operators


-- # Example 1

--example (m n : ℕ) (hm : odd m) (hn : odd n) : odd (m * n) :=
example : ∀ m n : ℕ, odd m → odd n → odd (m * n) :=
begin
  intros m n hm hn,
  rw odd at *, -- unnecessary
  cases hm with k hk,
  cases hn with l hl,
  rw [hk, hl],
  use 2*k*l + k +l,
  ring,
end


-- # Example 2

-- We can use `simp only [nat.succ_eq_add_one],` at any point if needed for clarity
-- Should I use for all notation?
example (n : ℕ) : ∑ i in range (n + 1), 2 * i = n * (n + 1) :=
begin
  induction n with n ih, { simp },
  suffices : n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2),
  { rw sum_range_succ,
    rw ih,
    assumption },
  ring,
end

-- Version using `calc`
example (n : ℕ) : ∑ i in range (n + 1), 2 * i = n * (n + 1) :=
begin
  induction n with n ih, { simp },
  calc  ∑ i in range (n + 2), 2 * i
      = ∑ i in range (n + 1), 2 * i + 2 * (n + 1) : by rw sum_range_succ
  ... = n * (n + 1) + 2 * (n + 1)                 : by rw ih
  ... = (n + 1) * (n + 2)                         : by ring,
end


-- # Example 3

-- Can also demonstrate with `{α : Type*} (s t : set α)` (or using a universe)
example (s t : set ℝ) (h : ∀ x, x ∈ s → x ∉ t) : s ∩ t = ∅ :=
begin
  ext x,
  rw mem_empty_eq,
  rw mem_inter_iff,
  rw iff_false,
  rw not_and,
  exact h x,
end
