/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import data.pnat.basic
import data.nat.parity
import algebra.big_operators.pi
import tactic.ring
import tactic.field_simp

/-!
# IMO 2013 Q1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

# Solution

Adaptation of the solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.
-/

open_locale big_operators

lemma arith_lemma (k n : ℕ) : 0 < 2 * n + 2^k.succ :=
calc 0 < 2                : zero_lt_two
   ... = 2^1              : (pow_one 2).symm
   ... ≤ 2^k.succ         : nat.pow_le_pow_of_le_right zero_lt_two (nat.le_add_left 1 k)
   ... ≤ 2 * n + 2^k.succ : nat.le_add_left _ _

lemma prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+):
      ∏ (i : ℕ) in finset.range k, ((1 : ℚ) + 1 / ↑(if i < k then m i else nm)) =
      ∏ (i : ℕ) in finset.range k, (1 + 1 / m i) :=
begin
  suffices : ∀ i, i ∈ finset.range k → (1 : ℚ) + 1 / ↑(if i < k then m i else nm) = 1 + 1 / m i,
  from finset.prod_congr rfl this,
  intros i hi,
  simp [finset.mem_range.mp hi]
end

theorem imo2013_q1 (n : ℕ+) (k : ℕ) :
    (∃ m : ℕ → ℕ+, (1 : ℚ) + (2^k - 1) / n = (∏ i in finset.range k, (1 + 1 / m i))) :=
begin
  revert n,
  induction k with pk hpk,
  { intro n, use (λ_, 1), simp }, -- For the base case, any m works.

  intro n,
  obtain ⟨t, ht : ↑n = 2 * t⟩ | ⟨t, ht : ↑n = 2 * t + 1⟩ := (n : ℕ).even_or_odd,
  { -- even case
    cases t, -- Eliminate the zero case to simplify later calculations.
    { exfalso, rw mul_zero at ht, exact pnat.ne_zero n ht },

    -- Now we have ht : ↑n = 2 * (t + 1).
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩,
    obtain ⟨pm, hpm⟩ := hpk t_succ,
    let m := λi, if i < pk then pm i else ⟨2 * t + 2^pk.succ, arith_lemma pk t⟩,
    use m,

    have hmpk : (m pk : ℚ) = 2 * t + 2^pk.succ,
    { have : m pk = ⟨2 * t + 2^pk.succ, _⟩ := if_neg (irrefl pk), simp [this] },

    have denom_ne_zero : (2 * (t:ℚ) + 2^pk.succ) ≠ 0,
    { norm_cast, exact (ne_of_gt $ arith_lemma pk t) },

    calc (1 : ℚ) + (2 ^ pk.succ - 1) / ↑n
        = 1 + (2 * 2 ^ pk - 1) / (2 * (t + 1) : ℕ)    : by rw [coe_coe n, ht, pow_succ]
    ... = (1 + 1 / (2 * t + 2 * 2^pk)) *
          (1 + (2 ^ pk - 1) / (↑t + 1))               : by { field_simp [t.cast_add_one_ne_zero],
                                                             ring }
    ... = (1 + 1 / (2 * t + 2^pk.succ)) *
          (1 + (2 ^ pk - 1) / t_succ)                 : by norm_cast
    ... = (∏ i in finset.range pk, (1 + 1 / m i)) *
          (1 + 1 / (m pk))                            : by rw [prod_lemma, hpm, ←hmpk, mul_comm]
    ... = ∏ i in finset.range pk.succ, (1 + 1 / m i)  : by rw ← finset.prod_range_succ _ pk },
  { -- odd case
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩,
    obtain ⟨pm, hpm⟩ := hpk t_succ,
    let m := λi, if i < pk then pm i else ⟨2 * t + 1, nat.succ_pos _⟩,
    use m,

    have hmpk : (m pk : ℚ) = 2 * t + 1,
    { have : m pk = ⟨2 * t + 1, _⟩ := if_neg (irrefl pk), simp [this] },

    have denom_ne_zero : (2 * (t : ℚ) + 1) ≠ 0 := by { norm_cast, apply (2 * t).succ_ne_zero },

    calc (1 : ℚ) + (2 ^ pk.succ - 1) / ↑n
        = 1 + (2 * 2^pk - 1) / (2 * t + 1 : ℕ)        : by rw [coe_coe n, ht, pow_succ]
    ... = (1 + 1 / (2 * t + 1)) *
          (1 + (2^pk - 1) / (t + 1))                  : by { field_simp [t.cast_add_one_ne_zero],
                                                             ring }
    ... = (1 + 1 / (2 * t + 1)) *
          (1 + (2^pk - 1) / t_succ)                   : by norm_cast
    ... = (∏ i in finset.range pk, (1 + 1 / m i)) *
          (1 + 1 / ↑(m pk))                           : by rw [prod_lemma, hpm, ←hmpk, mul_comm]
    ... = ∏ i in finset.range pk.succ, (1 + 1 / m i)  : by rw ← finset.prod_range_succ _ pk }
end
