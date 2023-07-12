/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.int.absolute_value
import linear_algebra.matrix.determinant

/-!
# Absolute values and matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some bounds on matrices involving absolute values.

## Main results

 * `matrix.det_le`: if the entries of an `n × n` matrix are bounded by `x`,
   then the determinant is bounded by `n! x^n`
 * `matrix.det_sum_le`: if we have `s` `n × n` matrices and the entries of each
   matrix are bounded by `x`, then the determinant of their sum is bounded by `n! (s * x)^n`
 * `matrix.det_sum_smul_le`: if we have `s` `n × n` matrices each multiplied by
   a constant bounded by `y`, and the entries of each matrix are bounded by `x`,
   then the determinant of the linear combination is bounded by `n! (s * y * x)^n`
-/

open_locale big_operators
open_locale matrix

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
  by rw [abv.map_units_int_smul, abv.map_prod])
... ≤ ∑ σ : perm n, (∏ (i : n), x) :
  sum_le_sum (λ _ _, prod_le_prod (λ _ _, abv.nonneg _) (λ _ _, hx _ _))
... = ∑ σ : perm n, x ^ (fintype.card n) : sum_congr rfl (λ _ _,
  by rw [prod_const, finset.card_univ])
... = nat.factorial (fintype.card n) • x ^ (fintype.card n) :
  by rw [sum_const, finset.card_univ, fintype.card_perm]

lemma det_sum_le {ι : Type*} (s : finset ι) {A : ι → matrix n n R}
  {abv : absolute_value R S} {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) :
  abv (det (∑ k in s, A k)) ≤
    nat.factorial (fintype.card n) • (finset.card s • x) ^ (fintype.card n) :=
det_le $ λ i j,
calc  abv ((∑ k in s, A k) i j)
    = abv (∑ k in s, A k i j) : by simp only [sum_apply]
... ≤ ∑ k in s, abv (A k i j) : abv.sum_le _ _
... ≤ ∑ k in s, x : sum_le_sum (λ k _, hx k i j)
... = s.card • x : sum_const _

lemma det_sum_smul_le {ι : Type*} (s : finset ι) {c : ι → R} {A : ι → matrix n n R}
  {abv : absolute_value R S}
  {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) {y : S} (hy : ∀ k, abv (c k) ≤ y) :
  abv (det (∑ k in s, c k • A k)) ≤
    nat.factorial (fintype.card n) • (finset.card s • y * x) ^ (fintype.card n) :=
by simpa only [smul_mul_assoc] using
det_sum_le s (λ k i j,
calc  abv (c k * A k i j)
    = abv (c k) * abv (A k i j) : abv.map_mul _ _
... ≤ y * x : mul_le_mul (hy k) (hx k i j) (abv.nonneg _) ((abv.nonneg _).trans (hy k)))

end matrix
