/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Alex J. Best
-/
import tactic.ring

/-!
# Hyperoperation sequence

This file defines the Hyperoperation sequence.
`hyperoperation 0 m k = k + 1`
`hyperoperation 1 m k = m + k`
`hyperoperation 2 m k = m * k`
`hyperoperation 3 m k = m ^ k`
`hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k)`

## References

* <https://en.wikipedia.org/wiki/Hyperoperation>

## Tags

hyperoperation
-/

/--
Implementation of the hyperoperation sequence
-/
def hyperoperation : ℕ → ℕ → ℕ → ℕ
| 0 _ k := k + 1
| 1 m 0 := m
| 2 _ 0 := 0
| (n + 3) _ 0 := 1
| (n + 1) m (k + 1) := hyperoperation n m (hyperoperation (n + 1) m k)

-- Basic hyperoperation lemmas

lemma hyperoperation_zero_eq_succ (m k : ℕ) : hyperoperation 0 m k = k + 1 :=
by rw hyperoperation

lemma hyperoperation_one_eq_self (m : ℕ) : hyperoperation 1 m 0 = m :=
begin
  rw hyperoperation,
end

lemma hyperoperation_2a0_0 (m : ℕ) : hyperoperation 2 m 0 = 0 :=
begin
  rw hyperoperation,
end

lemma hyperoperation_n3a0_1 (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 :=
begin
  rw hyperoperation,
end

lemma hyperoperation_n1ab1_recurse (n m k : ℕ) :
  hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) :=
begin
  cases n,
  rw hyperoperation,
  cases n;
  rw hyperoperation,
end

-- Interesting hyperoperation lemmas

lemma hyperoperation_1_addition (m k : ℕ) : hyperoperation 1 m k = m + k :=
begin
  induction k with bn bih,
  rw [nat_add_zero m, hyperoperation_1a0_a],
  rw [hyperoperation_n1ab1_recurse,bih,hyperoperation_0ab_b.succ],
  exact nat.add_assoc m bn 1,
end

lemma hyperoperation_2_multiplication (m k : ℕ) : hyperoperation 2 m k = m * k :=
begin
  induction k with bn bih,
  rw hyperoperation_2a0_0,
  exact (nat.mul_zero m).symm,
  rw [hyperoperation_n1ab1_recurse,hyperoperation_1_addition,bih],
  ring,
end

lemma hyperoperation_3_exponentiation (m k : ℕ) : hyperoperation 3 m k = m ^ k :=
begin
  induction k with bn bih,
  rw hyperoperation_n3a0_1,
  exact (pow_zero m).symm,
  rw [hyperoperation_n1ab1_recurse,hyperoperation_2_multiplication,bih],
  exact (pow_succ m bn).symm,
end

lemma hyperoperation_n2a1_a (n m : ℕ) : hyperoperation (n + 2) m 1 = m :=
begin
  induction n with nn nih,
  rw hyperoperation_2_multiplication,
  ring,
  rw [hyperoperation_n1ab1_recurse,hyperoperation_n3a0_1,nih],
end

lemma hyperoperation_succn_2_2_eq_4 (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 :=
begin
  induction n with nn nih,
  rw hyperoperation_1_addition,
  rw [hyperoperation_n1ab1_recurse,hyperoperation_n2a1_a,nih],
end
