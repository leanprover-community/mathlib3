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
import data.fintype.basic

def two_power_part (n : ℕ) := 2 ^ (padic_val_nat 2 n)

def odd_part (n : ℕ) := n / two_power_part n

lemma mul_two_power_part_odd_part (n : ℕ) : (two_power_part n) * (odd_part n) = n :=
begin
  have : two_power_part n ∣ n,
  { rw two_power_part,
    exact pow_padic_val_nat_dvd, },
  rw odd_part,
  exact nat.mul_div_cancel' this,
end

def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
a^(odd_part (n-1)) = 1 ∨ (∃ r : ℕ, r < padic_val_nat 2 (n-1) ∧ a^(2^r * odd_part(n-1)) = -1)


lemma square_roots_of_one {p : ℕ} [fact (p.prime)] {x : zmod p} (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  have root2 : x^2 -1 = 0,
  rw root,
  simp,
  have diffsquare : (x + 1) * (x - 1) = 0,
  ring_nf,
  exact root2,
  have zeros : (x + 1 = 0) ∨ (x - 1 = 0),
  exact zero_eq_mul.mp (eq.symm diffsquare),
  cases zeros with zero1 zero2,
  right,
  exact eq_neg_of_add_eq_zero zero1,
  left,
  exact sub_eq_zero.mp zero2,
end

lemma repeated_halving_of_exponent (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0)
  (e : ℕ) (h : a ^ e = 1) :
  a^(odd_part e) = 1 ∨ (∃ r : ℕ, r < padic_val_nat 2 e ∧ a^(2^r * odd_part e) = -1) :=
begin
  rw <-mul_two_power_part_odd_part e at h,
  rw two_power_part at h,
  revert h,
  induction padic_val_nat 2 e with i hi,
  { simp, },
  { intros h,
    simp [pow_succ, mul_assoc] at h,
    rw pow_mul' at h,
    have foo := square_roots_of_one h,
    cases foo with h1 h2,
    have roo := hi h1,
    cases roo with h3 h4,
    left,
    exact h3,
    right,
    cases h4 with r' hoo,
    use r',
    cases hoo with rr' a2,
    split,
    exact nat.lt.step rr',
    exact a2,
    right,


    have i : nat,
    exact p,
    use i,
    split,
     },
end

lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a :=
begin
  have fermat := zmod.pow_card_sub_one_eq_one ha, -- you'll need this lemma for this
  sorry,
end

lemma unlikely_strong_probable_prime_of_composite (n : ℕ) [fact (0 < n)]
  [decidable_pred (strong_probable_prime n)] (hp : ¬ n.prime) :
  ((finset.univ : finset (zmod n)).filter (strong_probable_prime n)).card ≤ n / 4 :=
begin
  -- TODO(Bolton): This will be a harder proof. Find some sublemmas that will be needed and
  -- extract them
end
