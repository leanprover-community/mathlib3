/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.nat.totient
import number_theory.quadratic_reciprocity

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`.
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.

## Implementation details
 * All of `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors

-/

open_locale classical
open_locale big_operators

variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `divisors 0 = ∅`. -/
def proper_divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 n)

/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisors_antidiagonal : finset (ℕ × ℕ) :=
((finset.Ico 1 (n + 1)).product (finset.Ico 1 (n + 1))).filter (λ x, x.fst * x.snd = n)

variable {n}

lemma not_proper_self : ¬ n ∈ proper_divisors n :=
begin
  rw proper_divisors,
  simp,
end

@[simp]
lemma mem_proper_divisors {m : ℕ} : n ∈ proper_divisors m ↔ n ∣ m ∧ n < m :=
begin
  rw proper_divisors,
  simp only [finset.Ico.mem, finset.mem_filter],
  refine ⟨λ h, ⟨h.2, h.1.2⟩, λ h, ⟨⟨_, h.2⟩, h.1⟩⟩,
  contrapose! h,
  rintro ⟨c, rfl⟩,
  simp [nat.le_zero_iff.1 (nat.lt_add_one_iff.1 h)]
end

lemma divisors_eq_proper_divisors_insert_self (posn : 0 < n) :
  divisors n = has_insert.insert n (proper_divisors n) :=
by rw [divisors, proper_divisors, finset.Ico.succ_top posn,
       finset.filter_insert, if_pos (dvd_refl n)]

@[simp]
lemma mem_divisors {m : ℕ} :
  n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0:=
begin
  cases m, {simp [divisors]},
  rw divisors_eq_proper_divisors_insert_self (nat.succ_pos m),
  simp only [ne.def, finset.mem_insert, mem_proper_divisors],
  split; intro h,
  { rcases h with ⟨rfl, _⟩, {simp [nat.succ_ne_zero]},
    refine ⟨h.1, λ hm, _⟩,
    rw hm at h,
    tauto },
  { by_cases heq : n = m.succ, {simp [heq]},
    right,
    exact ⟨h.1, lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h.1) heq⟩ }
end

@[simp]
lemma mem_divisors_antidiagonal {m : ℕ × ℕ} :
  m ∈ divisors_antidiagonal n ↔ m.fst * m.snd = n ∧ n ≠ 0 :=
begin
  simp only [divisors_antidiagonal, finset.Ico.mem, ne.def, finset.mem_filter, finset.mem_product],
  rw and_comm,
  apply and_congr_right,
  rintro rfl,
  split; intro h,
  { rintro h0, linarith },
  { repeat {rw [nat.add_one_le_iff, nat.pos_iff_ne_zero, ne.def, nat.lt_add_one_iff] },
    rw mul_eq_zero at h, rw decidable.not_or_iff_and_not at h,
    refine ⟨⟨h.1, _⟩, ⟨h.2, _⟩⟩,
    exact nat.le_mul_of_pos_right (nat.pos_of_ne_zero h.2),
    exact nat.le_mul_of_pos_left (nat.pos_of_ne_zero h.1), }
end

variable {n}

lemma divisor_le {m : ℕ}:
n ∈ divisors m → n ≤ m :=
begin
  rw divisors, simp only [and_imp, finset.Ico.mem, finset.mem_filter],
  intros a b c, omega,
end

variable (n)

def sum_divisors : ℕ :=
∑ i in divisors n, i

def sum_proper_divisors : ℕ :=
∑ i in proper_divisors n, i

@[simp]
lemma divisors_zero : divisors 0 = ∅ := by { ext, simp }

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
sum_divisors n = sum_proper_divisors n + n :=
begin
  rw sum_divisors,
  rw sum_proper_divisors,
  by_cases n = 0,
  { rw h,
    have h1 : proper_divisors 0 = ∅, ext, rw proper_divisors, simp,
    rw h1, simp },
  { rw divisors_eq_proper_divisors_insert_self,
    rw finset.sum_insert, rw add_comm,
    apply not_proper_self, omega, }
end
