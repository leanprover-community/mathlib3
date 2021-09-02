/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import algebra.absolute_value
import linear_algebra.matrix.determinant

/-!
# Absolute values and matrices

This file proves some bounds on matrices involving absolute values.
-/

open_locale big_operators
open_locale matrix

section move_me

lemma absolute_value.sum_le {ι R S : Type*} [semiring R] [ordered_semiring S]
  (abv : absolute_value R S) (s : finset ι) (f : ι → R) :
  abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ (λ i s hi ih, _),
  { simp },
  { simp only [finset.sum_insert hi],
    exact (abv.add_le _ _).trans (add_le_add (le_refl _) ih) },
end

@[simp]
lemma absolute_value.map_one' {R S : Type*} [comm_semiring R] [nontrivial R] [linear_ordered_ring S]
  (abv : absolute_value R S) : abv 1 = 1 :=
(mul_right_inj' $ show abv 1 ≠ 0, from abv.ne_zero one_ne_zero).mp $
show abv 1 * abv 1 = abv 1 * 1, by rw [← abv.map_mul, mul_one, mul_one]

lemma absolute_value.map_prod {ι R S : Type*} [comm_semiring R] [nontrivial R] [linear_ordered_comm_ring S]
  (abv : absolute_value R S) (s : finset ι) (f : ι → R) :
  abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ (λ i s hi ih, _),
  { simp only [finset.prod_empty, abv.map_one'] },
  { rw [finset.prod_insert hi, abv.map_mul, ih, finset.prod_insert hi] },
end

@[simp]
lemma absolute_value.map_units {R S : Type*} [comm_ring R] [nontrivial R] [linear_ordered_comm_ring S]
  (abv : absolute_value R S) (x : units ℤ) :
  abv ((x : ℤ) : R) = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

@[simp]
lemma absolute_value.map_units_smul {R S : Type*} [comm_ring R] [linear_ordered_comm_ring S]
  (abv : absolute_value R S) (x : units ℤ) (y : R) :
  abv (x • y) = abv y :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

end move_me

namespace matrix

open equiv finset

variables {R S : Type*} [comm_ring R] [nontrivial R] [linear_ordered_comm_ring S]
variables {n : Type*} [fintype n] [decidable_eq n]

lemma det_le {A : matrix n n R} {abv : absolute_value R S}
  {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
  abv A.det ≤ nat.factorial (fintype.card n) • x ^ (fintype.card n) :=
calc  abv A.det
    = abv (∑ σ : perm n, _) : congr_arg abv (det_apply _)
... ≤ ∑ σ : perm n, abv _ : abv.sum_le _ _
... = ∑ σ : perm n, (∏ i, abv (A (σ i) i)) : sum_congr rfl (λ σ hσ,
  by rw [abv.map_units_smul, abv.map_prod])
... ≤ ∑ σ : perm n, (∏ (i : n), x) :
  sum_le_sum (λ _ _, prod_le_prod (λ _ _, abv.nonneg _) (λ _ _, hx _ _))
... = ∑ σ : perm n, x ^ (fintype.card n) : sum_congr rfl (λ _ _,
  by rw [prod_const, finset.card_univ])
... = nat.factorial (fintype.card n) • x ^ (fintype.card n) :
  by rw [sum_const, finset.card_univ, fintype.card_perm]

lemma det_sum_le {ι : Type*} (s : finset ι) {c : ι → R} {A : ι → matrix n n R}
  {abv : absolute_value R S}
  {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) {y : S} (hy : ∀ k, abv (c k) ≤ y) :
  abv (det (∑ k in s, c k • A k)) ≤
    nat.factorial (fintype.card n) • (finset.card s • (x * y)) ^ (fintype.card n) :=
begin
  have : ∀ i j, abv ((∑ k in s, (c k • A k)) i j) ≤ finset.card s • (x * y),
  { intros i j,
    calc abv ((∑ k in s, (c k • A k)) i j)
        = abv (∑ k in s, (c k • A k) i j) : by simp only [sum_apply]
    ... ≤ ∑ k in s, abv ((c k • A k) i j) : abv.sum_le _ _
    ... = ∑ k in s, abv (A k i j) * abv (c k) : sum_congr rfl (λ k _,
      by simp only [pi.smul_apply, smul_eq_mul, mul_comm, abv.map_mul])
    ... ≤ ∑ k in s, x * y : sum_le_sum (λ k _, mul_le_mul (hx _ _ _) (hy _)
      (abv.nonneg _) (le_trans (abv.nonneg _) (hx k i j)))
    ... = s.card • (x * y) : sum_const _, },
  exact det_le this
end

end matrix
