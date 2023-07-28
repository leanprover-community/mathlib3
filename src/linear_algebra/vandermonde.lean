/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.big_operators.fin
import algebra.geom_sum
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nondegenerate

/-!
# Vandermonde matrix

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/

variables {R : Type*} [comm_ring R]

open equiv finset
open_locale big_operators matrix

namespace matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : fin n → R) : matrix (fin n) (fin n) R :=
λ i j, v i ^ (j : ℕ)

@[simp] lemma vandermonde_apply {n : ℕ} (v : fin n → R) (i j) :
  vandermonde v i j = v i ^ (j : ℕ) :=
rfl

@[simp] lemma vandermonde_cons {n : ℕ} (v0 : R) (v : fin n → R) :
  vandermonde (fin.cons v0 v : fin n.succ → R) =
    fin.cons (λ j, v0 ^ (j : ℕ)) (λ i, fin.cons 1 (λ j, v i * vandermonde v i j)) :=
begin
  ext i j,
  refine fin.cases (by simp) (λ i, _) i,
  refine fin.cases (by simp) (λ j, _) j,
  simp [pow_succ]
end

lemma vandermonde_succ {n : ℕ} (v : fin n.succ → R) :
  vandermonde v =
    fin.cons (λ j, v 0 ^ (j : ℕ))
      (λ i, fin.cons 1 (λ j, v i.succ * vandermonde (fin.tail v) i j)) :=
begin
  conv_lhs { rw [← fin.cons_self_tail v, vandermonde_cons] },
  simp only [fin.tail]
end

lemma vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : fin n → R) (i j) :
  (vandermonde v ⬝ (vandermonde w)ᵀ) i j = ∑ (k : fin n), (v i * w j) ^ (k : ℕ) :=
by simp only [vandermonde_apply, matrix.mul_apply, matrix.transpose_apply, mul_pow]

lemma vandermonde_transpose_mul_vandermonde {n : ℕ} (v : fin n → R) (i j) :
  ((vandermonde v)ᵀ ⬝ vandermonde v) i j = ∑ (k : fin n), v k ^ (i + j : ℕ) :=
by simp only [vandermonde_apply, matrix.mul_apply, matrix.transpose_apply, pow_add]

lemma det_vandermonde {n : ℕ} (v : fin n → R) :
  det (vandermonde v) = ∏ i : fin n, ∏ j in Ioi i, (v j - v i) :=
begin
  unfold vandermonde,

  induction n with n ih,
  { exact det_eq_one_of_card_eq_zero (fintype.card_fin 0) },

  calc det (of $ λ (i j : fin n.succ), v i ^ (j : ℕ))
      = det (of $ λ (i j : fin n.succ), matrix.vec_cons
               (v 0 ^ (j : ℕ))
               (λ i, v (fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :
    det_eq_of_forall_row_eq_smul_add_const (matrix.vec_cons 0 1) 0 (fin.cons_zero _ _) _
  ... = det (of $ λ (i j : fin n), matrix.vec_cons
               (v 0 ^ (j.succ : ℕ))
               (λ (i : fin n), v (fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
               (fin.succ_above 0 i)) :
    by simp_rw [det_succ_column_zero, fin.sum_univ_succ, of_apply, matrix.cons_val_zero, submatrix,
                of_apply, matrix.cons_val_succ,
                fin.coe_zero, pow_zero, one_mul, sub_self, mul_zero, zero_mul,
                finset.sum_const_zero, add_zero]
  ... = det (of $ λ (i j : fin n), (v (fin.succ i) - v 0) *
              (∑ k in finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ)) :
                matrix _ _ R) :
    by { congr, ext i j, rw [fin.succ_above_zero, matrix.cons_val_succ, fin.coe_succ, mul_comm],
         exact (geom_sum₂_mul (v i.succ) (v 0) (j + 1 : ℕ)).symm }
  ... = (∏ (i : fin n), (v (fin.succ i) - v 0)) * det (λ (i j : fin n),
    (∑ k in finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ))) :
    det_mul_column (λ i, v (fin.succ i) - v 0) _
  ... = (∏ (i : fin n), (v (fin.succ i) - v 0)) * det (λ (i j : fin n), v (fin.succ i) ^ (j : ℕ)) :
    congr_arg ((*) _) _
  ... = ∏ i : fin n.succ, ∏ j in Ioi i, (v j - v i) :
    by simp_rw [ih (v ∘ fin.succ), fin.prod_univ_succ, fin.prod_Ioi_zero, fin.prod_Ioi_succ],
  { intros i j,
    simp_rw [of_apply],
    rw matrix.cons_val_zero,
    refine fin.cases _ (λ i, _) i,
    { simp },
    rw [matrix.cons_val_succ, matrix.cons_val_succ, pi.one_apply],
    ring },
  { cases n,
    { simp only [det_eq_one_of_card_eq_zero (fintype.card_fin 0)] },
    apply det_eq_of_forall_col_eq_smul_add_pred (λ i, v 0),
    { intro j,
      simp },
    { intros i j,
      simp only [smul_eq_mul, pi.add_apply, fin.coe_succ, fin.coe_cast_succ, pi.smul_apply],
      rw [finset.sum_range_succ, add_comm, tsub_self, pow_zero, mul_one, finset.mul_sum],
      congr' 1,
      refine finset.sum_congr rfl (λ i' hi', _),
      rw [mul_left_comm (v 0), nat.succ_sub, pow_succ],
      exact nat.lt_succ_iff.mp (finset.mem_range.mp hi') } }
end

lemma det_vandermonde_eq_zero_iff [is_domain R] {n : ℕ} {v : fin n → R} :
  det (vandermonde v) = 0 ↔ ∃ (i j : fin n), v i = v j ∧ i ≠ j :=
begin
  split,
  { simp only [det_vandermonde v, finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index],
    exact λ i _ j h₁ h₂, ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩ },
  { simp only [ne.def, forall_exists_index, and_imp],
    refine λ i j h₁ h₂, matrix.det_zero_of_row_eq h₂ (funext $ λ k, _),
    rw [vandermonde_apply, vandermonde_apply, h₁], }
end

lemma det_vandermonde_ne_zero_iff [is_domain R] {n : ℕ} {v : fin n → R} :
  det (vandermonde v) ≠ 0 ↔ function.injective v :=
by simpa only [det_vandermonde_eq_zero_iff, ne.def, not_exists, not_and, not_not]

theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero {R : Type*} [comm_ring R]
  [is_domain R] {n : ℕ} {f v : fin n → R} (hf : function.injective f)
  (hfv : ∀ j, ∑ i : fin n, (f j ^ (i : ℕ)) * v i = 0) : v = 0 :=
eq_zero_of_mul_vec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)

theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero {R : Type*} [comm_ring R]
  [is_domain R] {n : ℕ} {f v : fin n → R} (hf : function.injective f)
  (hfv : ∀ j, ∑ i, v i * (f j ^ (i : ℕ)) = 0) : v = 0 :=
by { apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf, simp_rw mul_comm, exact hfv }

theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero {R : Type*} [comm_ring R]
  [is_domain R] {n : ℕ} {f v : fin n → R} (hf : function.injective f)
  (hfv : ∀ i : fin n, ∑ j : fin n, v j * (f j ^ (i : ℕ)) = 0) : v = 0 :=
eq_zero_of_vec_mul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)

end matrix
