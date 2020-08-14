/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import data.nat.modeq
import tactic.linarith

/-!
# Arithmetic

A basic arithmetic result needed to analyse the MIU system.
-/

open nat

private lemma le_pow2_and_pow2_eq_mod3' (c : ℕ) (x : ℕ) (h : c = 1 ∨ c = 2) :
  ∃ m : ℕ, c + 3*x ≤ 2^m ∧ 2^m % 3 = c % 3 :=
begin
  induction x with k hk,
  { use (c+1),
    cases h with hc hc;
    { rw hc, norm_num }, },
  rcases hk with ⟨g, hkg, hgmod⟩,
  by_cases hp : (c + 3*(k+1) ≤ 2 ^g),
  { use g, exact ⟨hp,hgmod⟩ },
  use (g+2),
  split,
  { rw [mul_succ, ←add_assoc,nat.pow_add],
    change 2^2 with (1+3), rw [mul_add (2^g) 1 3, mul_one],
    linarith [hkg,one_le_two_pow g], },
  rw [nat.pow_add,←mul_one c],
  exact modeq.modeq_mul hgmod rfl,
end

/--
If `a` is 1 or 2 modulo 3, then exists `k` a power of 2 for which `a ≤ k` and `a ≡ k [MOD 3]`.
-/
lemma le_pow2_and_pow2_eq_mod3 (a : ℕ) (h : a % 3 = 1 ∨ a % 3 = 2) :
  ∃ m : ℕ, a ≤ (pow 2 m) ∧ (pow 2 m) % 3 = a % 3:=
begin
  cases le_pow2_and_pow2_eq_mod3' (a%3) (a/3) h with m hm,
  use m,
  split,
  { convert hm.1, exact (mod_add_div a 3).symm, },
  rw [hm.2, mod_mod _ 3],
end
