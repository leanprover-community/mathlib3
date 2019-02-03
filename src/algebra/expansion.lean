/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.archimedean tactic.linarith

/-

This file provides decimal (and more generally base b>=2) expansions of "floor rings",
that is, ordered rings equipped with a floor function to the integers, such as
the rational or real numbers.

If r is an element of such a ring, then expansion.digit b r n is the (n+1)'st digit
after the decimal point in the base b expansion of r, so 0 <= expansion.digit b r n < b.
In other words, if aₙ = expansion.digit b r n then for a real number r, we have
r = (floor r) + 0.a₀a₁a₂... in base b. We have 0 ≤ aₙ < b (digit_lt_base).

-/

namespace expansion

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

def digit_aux (b : ℕ) (r : α) : ℕ → α
| 0 := (r - ⌊r⌋) * b
| (n + 1) := (digit_aux n - ⌊digit_aux n⌋) * b

lemma digit_aux_nonneg (b : ℕ) (r : α) (n : ℕ) : 0 ≤ digit_aux b r n :=
nat.cases_on n (mul_nonneg (sub_floor_nonneg _) (nat.cast_nonneg _))
  (λ _,(mul_nonneg (sub_floor_nonneg _) (nat.cast_nonneg _)))

lemma digit_aux_lt_base {b : ℕ} (hb : 0 < b) (r : α) (n : ℕ) : digit_aux b r n < b :=
nat.cases_on n
  ((mul_lt_iff_lt_one_left (show (0 : α) < b, by simp [hb])).2 (sub_floor_lt_one _))
  (λ n, (mul_lt_iff_lt_one_left (show (0 : α) < b, by simp [hb])).2 (sub_floor_lt_one _))

definition digit (b : ℕ) (r : α) (n : ℕ) := int.to_nat (⌊digit_aux b r n⌋)

lemma digit_lt_base {b : ℕ} (hb : 0 < b) (r : α) (n : ℕ) : digit b r n < b :=
begin
  have h : (⌊digit_aux b r n⌋ : α) < b,
    exact lt_of_le_of_lt (floor_le _) (digit_aux_lt_base hb r n),
  have h2 : ⌊digit_aux b r n⌋ = digit b r n,
    exact (int.to_nat_of_nonneg (floor_nonneg.2 $ digit_aux_nonneg b r n)).symm,
  have h3 : ((digit b r n : ℤ) : α) < b,
     rwa ←h2,
  simpa using h3,
end

theorem approx {b : ℕ} (hb : 0 < b) (r : α) (n : ℕ) :
⌊((r - ⌊r⌋) * b ^ n)⌋ = finset.sum (finset.range n) (λ i, digit b r i) :=
begin
  induction n with m hm,
  { rw [pow_zero,mul_one,finset.range_zero,finset.sum_empty,←floor_of_bounds],
    exact ⟨sub_floor_nonneg _,by convert (sub_floor_lt_one _);simp⟩
  },
  sorry
end

end expansion
