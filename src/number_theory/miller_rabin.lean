/-
Copyright (c) 2022 Bolton Bailey, Sean Golinski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Sean Golinski
-/

import data.fintype.basic
import group_theory.order_of_element
import tactic.zify
import data.nat.totient
import data.zmod.basic
import number_theory.padics.padic_norm
import field_theory.finite.basic


def two_power_part (n : ℕ) := 2 ^ (padic_val_nat 2 n)

def odd_part (n : ℕ) := n / two_power_part n

lemma mul_two_power_part_odd_part (n : ℕ) : (two_power_part n) * (odd_part n) = n :=
begin
  sorry,
end

def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
a^(odd_part (n-1)) = 1 ∨ (∃ k i : ℕ, n = 2^i * k ∧ a^k = -1)


lemma square_roots_of_one (p : ℕ) [fact (p.prime)] (x : zmod p) (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  have root2 : x^2 -1 = 0,
  rw root,
  simp,
  have diffsquare : (x + 1) * (x - 1) = 0,
  ring_nf,
  exact root2,
  have zeros : (x + 1 = 0) ∨ (x - 1 = 0),
  -- rw ← zero_eq_mul,
  -- rw ← diffsquare,
  exact zero_eq_mul.mp (eq.symm diffsquare),
  cases zeros with zero1 zero2,
  right,
  exact eq_neg_of_add_eq_zero zero1,
  left,
  exact sub_eq_zero.mp zero2,
end

example (p q : Prop) : (¬ p -> q) -> p ∨ q :=
begin
  exact or_iff_not_imp_left.mpr,
end

lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a :=
begin
  unfold strong_probable_prime,
  -- unfold odd_part,
  -- unfold two_power_part,
  apply or_iff_not_imp_left.mpr,
  intro base,
  by_contra,
  simp_rw not_exists at h,
  have : (∀ i : ℕ, ¬ a ^ (2^i * odd_part (p - 1)) = 1),
  { intro i,
    induction i with i hi,
    { sorry, },
    { intro h2,
      apply hi, clear hi,
      have hsq : (a ^ (2 ^ i * odd_part (p - 1))) ^ 2 = 1,
      { sorry, },
      sorry, }, },
  have foo := this ((padic_val_nat 2 (p-1))),
  apply foo,
  sorry,
end
