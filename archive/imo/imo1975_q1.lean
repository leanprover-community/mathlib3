/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import data.real.basic
import data.nat.interval
import algebra.order.rearrangement
import algebra.big_operators.ring

/-!
# IMO 1975 Q1

Let `x₁, x₂, ... , xₙ` and `y₁, y₂, ... , yₙ` be two sequences of real numbers, such that
`x₁ ≥ x₂ ≥ ... ≥ xₙ` and `y₁ ≥ y₂ ≥ ... ≥ yₙ`. Prove that if `z₁, z₂, ... , zₙ` is any permutation
of `y₁, y₂, ... , yₙ`, then `∑ (xᵢ - yᵢ)^2 ≤ ∑ (xᵢ - zᵢ)^2`

# Solution

Firstly, we expand the squares withing both sums and distribute into separate finite sums. Then,
noting that `∑ yᵢ ^ 2 = ∑ zᵢ ^ 2`, it remains to prove that `∑ xᵢ * zᵢ ≤ ∑ xᵢ * yᵢ`, which is true
by the Rearrangement Inequality
-/

open_locale big_operators

/- Let `n` be a natural number, `x` and `y` be as in the problem statement and `σ` be the
permutation of natural numbers such that `z = y ∘ σ` -/
variables (n : ℕ) (σ : equiv.perm ℕ) (hσ : {x | σ x ≠ x} ⊆ finset.Icc 1 n) (x y : ℕ → ℝ)
variables (hx : antitone_on x (finset.Icc 1 n))
variables (hy : antitone_on y (finset.Icc 1 n))
include hx hy hσ

theorem IMO_1975_Q1 :
  ∑ i in finset.Icc 1 n, (x i - y i) ^ 2 ≤ ∑ i in finset.Icc 1 n, (x i - y (σ i)) ^ 2 :=
begin
  simp only [sub_sq, finset.sum_add_distrib, finset.sum_sub_distrib],
  -- a finite sum is invariant if we permute the order of summation
  have hσy : ∑ (i : ℕ) in finset.Icc 1 n, y i ^ 2 = ∑ (i : ℕ) in finset.Icc 1 n, y (σ i) ^ 2,
  { rw ← equiv.perm.sum_comp σ (finset.Icc 1 n) _ hσ },
  -- let's cancel terms appearing on both sides
  norm_num [hσy, mul_assoc, ← finset.mul_sum],
  -- what's left to prove is a version of the rearrangement inequality
  apply monovary_on.sum_mul_comp_perm_le_sum_mul _ hσ,
  -- finally we need to show that `x` and `y` 'vary' together on `[1, n]` and this is due to both of
  -- them being `decreasing`
  exact antitone_on.monovary_on hx hy
end
