/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.big_operators.basic
import tactic

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `nat` namespace:
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
 * `perfect n` is true when the sum of `proper_divisors n` is `n`.

## Implementation details
 * `divisors 0` is defined to be `{0}`, while
`proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/

open_locale classical
open_locale big_operators

namespace nat
variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = {0}`. -/
def divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.range (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def proper_divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.range n)

/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisors_antidiagonal : finset (ℕ × ℕ) :=
((finset.Ico 1 (n + 1)).product (finset.Ico 1 (n + 1))).filter (λ x, x.fst * x.snd = n)

variable {n}

lemma proper_divisors.not_self_mem : ¬ n ∈ proper_divisors n :=
begin
  rw proper_divisors,
  simp,
end

@[simp]
lemma mem_proper_divisors {m : ℕ} : n ∈ proper_divisors m ↔ n ∣ m ∧ n < m :=
begin
  rw [proper_divisors, and_comm],
  simp,
end

lemma divisors_eq_proper_divisors_insert_self :
  divisors n = has_insert.insert n (proper_divisors n) :=
by rw [divisors, proper_divisors, finset.range_succ, finset.filter_insert, if_pos (dvd_refl n)]

@[simp]
lemma mem_divisors {m : ℕ} :
  n ∈ divisors m ↔ if (m = 0) then n = 0 else n ∣ m :=
begin
  cases m,
  { simp [divisors] },
  simp only [divisors, if_neg m.succ_ne_zero, lt_succ_iff, and_iff_right_iff_imp, finset.mem_filter,
             finset.mem_range],
  exact nat.le_of_dvd (nat.succ_pos m)
end

@[simp]
lemma mem_divisors_antidiagonal {x : ℕ × ℕ} :
  x ∈ divisors_antidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 :=
begin
  simp only [divisors_antidiagonal, finset.Ico.mem, ne.def, finset.mem_filter, finset.mem_product],
  rw and_comm,
  apply and_congr_right,
  rintro rfl,
  split; intro h,
  { rintro h0,
    linarith },
  { repeat {rw [nat.add_one_le_iff, nat.pos_iff_ne_zero, ne.def, nat.lt_add_one_iff] },
    rw [mul_eq_zero, decidable.not_or_iff_and_not] at h,
    refine ⟨⟨h.1, _⟩, ⟨h.2, _⟩⟩,
    exact nat.le_mul_of_pos_right (nat.pos_of_ne_zero h.2),
    exact nat.le_mul_of_pos_left (nat.pos_of_ne_zero h.1), }
end

variable {n}

lemma divisor_le {m : ℕ}:
n ∈ divisors m → n ≤ m :=
begin
  cases m,
  { simp },
  simp only [mem_divisors, if_neg (nat.succ_ne_zero m)],
  exact nat.le_of_dvd (nat.succ_pos m),
end

variable (n)

@[simp]
lemma divisors_zero : divisors 0 = {0} := by { ext, simp }

@[simp]
lemma proper_divisors_zero : proper_divisors 0 = ∅ := by { ext, simp }

@[simp]
lemma divisors_antidiagonal_zero : divisors_antidiagonal 0 = ∅ := by { ext, simp }

@[simp]
lemma divisors_antidiagonal_one : divisors_antidiagonal 1 = {(1,1)} :=
by { ext, simp [nat.mul_eq_one_iff, prod.ext_iff], }

lemma swap_mem_divisors_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.swap ∈ divisors_antidiagonal n :=
begin
  rw [mem_divisors_antidiagonal, mul_comm] at h,
  simpa,
end

lemma fst_mem_divisors_of_mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.fst ∈ divisors n :=
begin
  rw mem_divisors_antidiagonal at h,
  simp [dvd.intro _ h.1, h.2],
end

lemma snd_mem_divisors_of_mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) :
  x.snd ∈ divisors n :=
begin
  rw mem_divisors_antidiagonal at h,
  simp [dvd.intro_left _ h.1, h.2],
end

@[simp]
lemma map_swap_divisors_antidiagonal {n : ℕ} :
  (divisors_antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩
  = divisors_antidiagonal n :=
begin
  ext,
  simp only [exists_prop, mem_divisors_antidiagonal, finset.mem_map, function.embedding.coe_fn_mk,
             ne.def, prod.swap_prod_mk, prod.exists],
  split,
  { rintros ⟨x, y, ⟨⟨rfl, h⟩, rfl⟩⟩,
    simp [h, mul_comm] },
  { rintros ⟨rfl, h⟩,
    use [a.snd, a.fst],
    simp [h, mul_comm] }
end

lemma sum_divisors_eq_sum_proper_divisors_add_self :
∑ i in divisors n, i = ∑ i in proper_divisors n, i + n :=
begin
  cases n,
  { simp },
  { rw [divisors_eq_proper_divisors_insert_self,
        finset.sum_insert (proper_divisors.not_self_mem), add_comm] }
end

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n`. -/
def perfect (n : ℕ) : Prop := ∑ i in proper_divisors n, i = n

theorem perfect_iff_sum_proper_divisors {n : ℕ} :
  perfect n ↔ ∑ i in proper_divisors n, i = n := iff.rfl

theorem perfect_iff_sum_divisors_eq_two_mul {n : ℕ} :
  perfect n ↔ ∑ i in divisors n, i = 2 * n :=
begin
  rw [perfect, sum_divisors_eq_sum_proper_divisors_add_self, two_mul],
  split; intro h,
  { rw h },
  { apply add_right_cancel h }
end

end nat
