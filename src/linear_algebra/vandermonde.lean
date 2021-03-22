/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import group_theory.perm.fin
import linear_algebra.determinant

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/

variables {R : Type*} [comm_ring R]

open_locale big_operators
open_locale matrix

namespace matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : fin n → R) : matrix (fin n) (fin n) R
| i j := v i ^ (j : ℕ)

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

lemma det_succ_row {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) :
  det A = ∑ j : fin n.succ, (-1) ^ (j : ℕ) * A 0 j *
    det (λ (i' j' : fin n), A i'.succ (j.succ_above j')) :=
begin
  rw [matrix.det, finset.univ_perm_fin_succ, ← finset.univ_product_univ],
  simp only [finset.sum_map, equiv.to_embedding_apply, finset.sum_product],
  refine finset.sum_congr rfl (λ j _, _),
  simp only [fin.prod_univ_succ, matrix.det, finset.mul_sum],
  refine fin.cases _ (λ j, _) j,
  { simp only [equiv.perm.decompose_fin_symm_apply_zero, fin.coe_zero, one_mul,
        equiv.perm.decompose_fin.symm_sign, equiv.swap_self, if_true, id.def, eq_self_iff_true,
        equiv.perm.decompose_fin_symm_apply_succ, fin.succ_above_zero, equiv.coe_refl, pow_zero,
        mul_left_comm] },
  { simp only [fin.succ_ne_zero j, pow_succ, neg_mul_eq_neg_mul_symm,
         equiv.perm.decompose_fin_symm_apply_zero, one_mul, equiv.perm.decompose_fin.symm_sign,
         fin.coe_succ, units.neg_mul, if_false, neg_inj, equiv.perm.decompose_fin_symm_apply_succ,
         finset.sum_neg_distrib, int.cast_neg, units.coe_neg],
    sorry }
end

lemma det_vandermonde {n : ℕ} (v : fin n → R) :
  det (vandermonde v) = ∏ i : fin n, ∏ j in finset.univ.filter (λ j, i < j), (v j - v i) :=
begin
  induction n with n ih,
  { exact det_eq_one_of_card_eq_zero (fintype.card_fin 0) },

  rw vandermonde_succ,

  calc det (λ (i j : fin n.succ), v j ^ (i : ℕ))
      = det (λ i, fin.cons (v 0 ^ (i : ℕ)) (λ j, v j.succ ^ (i : ℕ) - v 0 ^ (i : ℕ))) :
        det_eq_of_column_eq_add_zero _ _ (λ _, 1) _ _
  ... = det (λ (i j : fin n), @fin.cons _ (λ _, R)
              (v 0 ^ (i.succ : ℕ))
              (λ (j : fin n), v j.succ ^ (i.succ : ℕ) - v 0 ^ (i.succ : ℕ))
              (fin.succ_above 0 j)) :
    by simp_rw [det_succ_column, fin.sum_univ_succ, fin.cons_zero, fin.cons_succ, fin.coe_zero,
                pow_zero, sub_self, one_mul, mul_zero, zero_mul, finset.sum_const_zero, add_zero]
  ... = det (λ (i j : fin n), (v j.succ - v 0) *
              (∑ k in finset.range (i + 1 : ℕ), v j.succ ^ k * v 0 ^ (i - k : ℕ))) :
    by { congr, ext i j, rw [fin.succ_above_zero, fin.cons_succ, fin.coe_succ, sub_mul_sum_pow] }
  ... = (∏ (j : fin n), (v j.succ - v 0)) * det (λ (i j : fin n),
    (∑ k in finset.range (i + 1 : ℕ), v j.succ ^ k * v 0 ^ (i - k : ℕ))) :
    det_row_mul (λ j, v j.succ - v 0) _
  ... = (∏ (j : fin n), (v j.succ - v 0)) * det (λ (i j : fin n), v j.succ ^ (i : ℕ)) :
    congr_arg ((*) _) _
  ... = ∏ i : fin n.succ, ∏ j in finset.univ.filter (λ j, i < j), (v j - v i) :
    by { simp_rw [ih, fin.prod_univ_succ, prod_filter_zero_lt, prod_filter_succ_lt] },
  { intro i, rw fin.cons_zero },
  { intros i j, rw [fin.cons_succ, one_mul, sub_add_cancel] },
  { cases n,
    { simp [det] },
    apply det_eq_of_row_eq_add_pred _ _ (λ i, v 0),
    { ext j,
      simp },
    { intro i, ext j,
      simp only [smul_eq_mul, pi.add_apply, fin.coe_succ, fin.coe_cast_succ, pi.smul_apply],
      rw [finset.sum_range_succ, nat.sub_self, pow_zero, mul_one, finset.mul_sum],
      congr' 1,
      refine finset.sum_congr rfl (λ i' hi', _),
      rw [mul_left_comm (v 0), nat.succ_sub, pow_succ],
      exact nat.lt_succ_iff.mp (finset.mem_range.mp hi') } }
end

end matrix
