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

def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
let s := padic_val_nat 2 (n - 1), d := (n-1)/2^s in
  a^d = 1 ∨ (∃ r : ℕ, r < s ∧ a^(2^r * d) = -1)


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


lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a :=
begin
  unfold strong_probable_prime,
  simp only [],
  induction padic_val_nat 2 (p - 1) with s hs,
  { sorry, },
  { cases hs,
    { sorry, },
    { sorry, }, },
end
