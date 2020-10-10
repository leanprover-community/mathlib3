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
 * `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/

open_locale classical
open_locale big_operators

namespace nat
variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def proper_divisors : finset ℕ := finset.filter (λ x : ℕ, x ∣ n) (finset.Ico 1 n)

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
  rw [proper_divisors, finset.mem_filter, finset.Ico.mem, and_comm],
  apply and_congr_right,
  rw and_iff_right_iff_imp,
  intros hdvd hlt,
  apply nat.pos_of_ne_zero _,
  rintro rfl,
  rw zero_dvd_iff.1 hdvd at hlt,
  apply lt_irrefl 0 hlt,
end

lemma divisors_eq_proper_divisors_insert_self_of_pos (h : 0 < n):
  divisors n = has_insert.insert n (proper_divisors n) :=
by rw [divisors, proper_divisors, finset.Ico.succ_top h, finset.filter_insert, if_pos (dvd_refl n)]

@[simp]
lemma mem_divisors {m : ℕ} :
  n ∈ divisors m ↔ (n ∣ m ∧ m ≠ 0) :=
begin
  cases m,
  { simp [divisors] },
  simp only [divisors, finset.Ico.mem, ne.def, finset.mem_filter, succ_ne_zero, and_true,
             and_iff_right_iff_imp, not_false_iff],
  intro hdvd,
  split,
  { apply nat.pos_of_ne_zero,
    rintro rfl,
    apply nat.succ_ne_zero,
    rwa zero_dvd_iff at hdvd },
  { rw nat.lt_succ_iff,
    apply nat.le_of_dvd (nat.succ_pos m) hdvd }
end

lemma dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m :=
begin
  cases m,
  { apply dvd_zero },
  { simp [mem_divisors.1 h], }
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
  { contrapose! h, simp [h], },
  { rw [nat.lt_add_one_iff, nat.lt_add_one_iff],
    rw [mul_eq_zero, decidable.not_or_iff_and_not] at h,
    simp only [succ_le_of_lt (nat.pos_of_ne_zero h.1), succ_le_of_lt (nat.pos_of_ne_zero h.2),
               true_and],
    exact ⟨le_mul_of_pos_right (nat.pos_of_ne_zero h.2),
      le_mul_of_pos_left (nat.pos_of_ne_zero h.1)⟩ }
end

variable {n}

lemma divisor_le {m : ℕ}:
n ∈ divisors m → n ≤ m :=
begin
  cases m,
  { simp },
  simp only [mem_divisors, m.succ_ne_zero, and_true, ne.def, not_false_iff],
  exact nat.le_of_dvd (nat.succ_pos m),
end

variable (n)

@[simp]
lemma divisors_zero : divisors 0 = ∅ := by { ext, simp }

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
  simp [h.1, h.2],
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
    simp [mul_comm, h], },
  { rintros ⟨rfl, h⟩,
    use [a.snd, a.fst],
    rw mul_comm,
    simp [h] }
end

lemma sum_divisors_eq_sum_proper_divisors_add_self :
∑ i in divisors n, i = ∑ i in proper_divisors n, i + n :=
begin
  cases n,
  { simp },
  { rw [divisors_eq_proper_divisors_insert_self_of_pos (nat.succ_pos _),
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

lemma mem_divisors_prime_pow {p : ℕ} (pp : p.prime) (k : ℕ) {x : ℕ} :
  x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ) (H : j ≤ k), x = p ^ j :=
by rw [mem_divisors, nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]

lemma divisors_prime {p : ℕ} (pp : p.prime) :
  divisors p = {1, p} :=
begin
  ext,
  simp only [pp.ne_zero, and_true, ne.def, not_false_iff, finset.mem_insert,
    finset.mem_singleton, mem_divisors],
  refine ⟨pp.2 a, λ h, _⟩,
  rcases h; subst h,
  apply one_dvd,
end

lemma divisors_prime_pow {p : ℕ} (pp : p.prime) (k : ℕ) :
  divisors (p ^ k) = (finset.range (k + 1)).map ⟨pow p, pow_right_injective pp.two_le⟩ :=
by { ext, simp [mem_divisors_prime_pow, pp, nat.lt_succ_iff, @eq_comm _ a] }

open finset

@[simp]
lemma sum_divisors_prime {α : Type*} [add_comm_monoid α] {p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∑ x in p.divisors, f x = f p + f 1 :=
begin
  simp only [h, divisors_prime],
  rw [sum_insert, sum_singleton, add_comm],
  rw mem_singleton,
  apply h.ne_one.symm,
end

@[simp]
lemma prod_divisors_prime {α : Type*} [comm_monoid α] {p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∏ x in p.divisors, f x = f p * f 1 :=
@sum_divisors_prime (additive α) _ _ _ h

@[simp]
lemma sum_divisors_prime_pow {α : Type*} [add_comm_monoid α] {k p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∑ x in (p ^ k).divisors, f x = ∑ x in range (k + 1), f (p ^ x) :=
by simp [h, divisors_prime_pow]

@[simp]
lemma prod_divisors_prime_pow {α : Type*} [comm_monoid α] {k p : ℕ} {f : ℕ → α} (h : p.prime) :
  ∏ x in (p ^ k).divisors, f x = ∏ x in range (k + 1), f (p ^ x) :=
@sum_divisors_prime_pow (additive α) _ _ _ _ h

end nat
