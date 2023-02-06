/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Eric Wieser
-/
import tactic.ring
import data.nat.parity

/-!
# Hyperoperation sequence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the Hyperoperation sequence.
`hyperoperation 0 m k = k + 1`
`hyperoperation 1 m k = m + k`
`hyperoperation 2 m k = m * k`
`hyperoperation 3 m k = m ^ k`
`hyperoperation (n + 3) m 0 = 1`
`hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k)`

## References

* <https://en.wikipedia.org/wiki/Hyperoperation>

## Tags

hyperoperation
-/

/--
Implementation of the hyperoperation sequence
where `hyperoperation n m k` is the `n`th hyperoperation between `m` and `k`.
-/
def hyperoperation : ℕ → ℕ → ℕ → ℕ
| 0 _ k := k + 1
| 1 m 0 := m
| 2 _ 0 := 0
| (n + 3) _ 0 := 1
| (n + 1) m (k + 1) := hyperoperation n m (hyperoperation (n + 1) m k)

-- Basic hyperoperation lemmas

@[simp] lemma hyperoperation_zero (m : ℕ) : hyperoperation 0 m = nat.succ :=
funext $ λ k, by rw [hyperoperation, nat.succ_eq_add_one]

lemma hyperoperation_ge_three_eq_one (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 :=
by rw hyperoperation

lemma hyperoperation_recursion (n m k : ℕ) :
  hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) :=
by obtain (_|_|_) := n; rw hyperoperation

-- Interesting hyperoperation lemmas

@[simp] lemma hyperoperation_one : hyperoperation 1 = (+) :=
begin
  ext m k,
  induction k with bn bih,
  { rw [nat_add_zero m, hyperoperation], },
  { rw [hyperoperation_recursion, bih, hyperoperation_zero],
    exact nat.add_assoc m bn 1, },
end

@[simp] lemma hyperoperation_two : hyperoperation 2 = (*) :=
begin
  ext m k,
  induction k with bn bih,
  { rw hyperoperation,
    exact (nat.mul_zero m).symm, },
  { rw [hyperoperation_recursion, hyperoperation_one, bih],
    ring, },
end

@[simp] lemma hyperoperation_three : hyperoperation 3 = (^) :=
begin
  ext m k,
  induction k with bn bih,
  { rw hyperoperation_ge_three_eq_one,
    exact (pow_zero m).symm, },
  { rw [hyperoperation_recursion, hyperoperation_two, bih],
    exact (pow_succ m bn).symm, },
end

lemma hyperoperation_ge_two_eq_self (n m : ℕ) : hyperoperation (n + 2) m 1 = m :=
begin
  induction n with nn nih,
  { rw hyperoperation_two,
    ring, },
  { rw [hyperoperation_recursion, hyperoperation_ge_three_eq_one, nih], },
end

lemma hyperoperation_two_two_eq_four (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 :=
begin
  induction n with nn nih,
  { rw hyperoperation_one, },
  { rw [hyperoperation_recursion, hyperoperation_ge_two_eq_self, nih], },
end

lemma hyperoperation_ge_three_one (n : ℕ) : ∀ (k : ℕ), hyperoperation (n + 3) 1 k = 1 :=
begin
  induction n with nn nih,
  { intros k,
    rw [hyperoperation_three, one_pow], },
  { intros k,
    cases k,
    { rw hyperoperation_ge_three_eq_one, },
    { rw [hyperoperation_recursion, nih], }, },
end

lemma hyperoperation_ge_four_zero (n k : ℕ) :
  hyperoperation (n + 4) 0 k = if (even k) then 1 else 0 :=
begin
  induction k with kk kih,
  { rw hyperoperation_ge_three_eq_one,
    simp only [even_zero, if_true], },
  { rw hyperoperation_recursion,
    rw kih,
    simp_rw nat.even_add_one,
    split_ifs,
    { exact hyperoperation_ge_two_eq_self (n + 1) 0, },
    { exact hyperoperation_ge_three_eq_one n 0, }, },
end
