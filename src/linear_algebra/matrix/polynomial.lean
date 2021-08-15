/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import linear_algebra.matrix.determinant
import data.polynomial.eval
import data.polynomial.monic
import algebra.polynomial.big_operators

/-!
# Matrices of polynomials and polynomials of matrices

In this file, we prove results about matrices over a polynomial ring.
In particular, we give results about the polynomial given by
`det (t * I + A)`.

## References

  * "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3

## Tags

matrix determinant, polynomial
-/

open_locale matrix big_operators

variables {n α : Type*} [decidable_eq n] [fintype n] [comm_ring α]

open polynomial matrix equiv.perm

namespace polynomial

lemma nat_degree_det_X_add_C_le (A B : matrix n n α) :
  nat_degree (det ((X : polynomial α) • A.map C + B.map C)) ≤ fintype.card n :=
begin
  rw det_apply,
  refine (nat_degree_sum_le _ _).trans _,
  refine (multiset.max_le_of_forall_le _ _ _),
  { simp only [forall_apply_eq_imp_iff', true_and, function.comp_app, multiset.map_map,
               multiset.mem_map, exists_imp_distrib, finset.mem_univ_val],
    intros g,
    suffices : (∏ (i : n), (X • A.map C + B.map C) (g i) i).nat_degree ≤
      fintype.card n,
    { cases int.units_eq_one_or (sign g) with sg sg,
      { rw [sg, one_smul],
        exact this },
      { rw [sg, units.neg_smul, one_smul, nat_degree_neg],
        exact this } },
    refine (nat_degree_multiset_prod_le _).trans _,
    refine (multiset.sum_le_of_forall_le _ 1 _).trans _,
    { simp only [forall_apply_eq_imp_iff', true_and, algebra.id.smul_eq_mul, function.comp_app,
                 ring_hom.map_matrix_apply, multiset.map_map, map_apply, multiset.mem_map,
                 dmatrix.add_apply, pi.smul_apply, exists_imp_distrib, finset.mem_univ_val],
      intro,
      refine (nat_degree_add_le _ _).trans _,
      simpa using (nat_degree_mul_C_le _ _).trans nat_degree_X_le },
    { simpa [fintype.card] } }
end

lemma coeff_det_X_add_C_zero (A B : matrix n n α) :
  coeff (det ((X : polynomial α) • A.map C + B.map C)) 0 = det B :=
begin
  rw [det_apply, coeff_finset_sum, det_apply],
  refine finset.sum_congr rfl _,
  intros g hg,
  convert coeff_smul (sign g) _ 0,
  rw coeff_zero_prod,
  refine finset.prod_congr rfl _,
  simp
end

lemma coeff_det_X_add_C_card (A B : matrix n n α) :
  coeff (det ((X : polynomial α) • A.map C + B.map C)) (fintype.card n) = det A :=
begin
  rw [det_apply, det_apply, coeff_finset_sum],
  refine finset.sum_congr rfl _,
  simp only [algebra.id.smul_eq_mul, finset.mem_univ, ring_hom.map_matrix_apply, forall_true_left,
             map_apply, dmatrix.add_apply, pi.smul_apply],
  intros g,
  convert coeff_smul (sign g) _ _,
  rw ←mul_one (fintype.card n),
  convert (coeff_prod_of_nat_degree_le _ _ _ _).symm,
  { ext,
    simp [coeff_C] },
  { intros p hp,
    refine (nat_degree_add_le _ _).trans _,
    simpa using (nat_degree_mul_C_le _ _).trans nat_degree_X_le }
end

lemma leading_coeff_det_X_one_add_C (A : matrix n n α) :
  leading_coeff (det ((X : polynomial α) • (1 : matrix n n (polynomial α)) + A.map C)) = 1 :=
begin
  casesI (subsingleton_or_nontrivial α),
  { simp },
  rw [←@det_one n, ←coeff_det_X_add_C_card _ A, leading_coeff],
  simp only [matrix.map_one, C_eq_zero, ring_hom.map_one],
  cases (nat_degree_det_X_add_C_le 1 A).eq_or_lt with h h,
  { simp only [ring_hom.map_one, matrix.map_one, C_eq_zero] at h,
    rw h },
  { -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_nat_degree_lt h,
    rw coeff_det_X_add_C_card at H,
    simpa using H }
end

end polynomial
