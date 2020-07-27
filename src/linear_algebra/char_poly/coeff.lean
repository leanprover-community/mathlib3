/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark.
-/

import linear_algebra.char_poly
import linear_algebra.matrix
import ring_theory.polynomial.basic
import algebra.polynomial.big_operators
import group_theory.perm.cycles

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `degree_char_poly_eq_dim` proves that the degree of the characterist polynomial
  over a nonzero ring is the dimension of the matrix
- `det_eq_char_poly` proves that the determinant is the constant term of the characteristic
  polynomial, up to sign.
- `trace_eq_char_poly` proves that the trace is the negative of the (d-1)th coefficient of the
  characteristic polynomial, where d is the dimension of the matrix. 
  For a nonzero ring, this is the second-highest coefficient.

-/

noncomputable theory

universes u v w z

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n G : Type v} [fintype n] [decidable_eq n]
variables {α β : Type v} [decidable_eq α]


open finset
open polynomial

variable {M : matrix n n R}

lemma char_matrix_apply_nat_degree [nontrivial R] (i j : n) :
  (char_matrix M i j).nat_degree = ite (i = j) 1 0 :=
by { by_cases i = j; simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (nat.succ_pos 0)], }

lemma char_matrix_apply_nat_degree_le (i j : n) :
  (char_matrix M i j).nat_degree ≤ ite (i = j) 1 0 :=
by split_ifs; simp [h, nat_degree_X_sub_C_le]

variable (M)
lemma char_poly_sub_diagonal_degree_lt :
(char_poly M - ∏ (i : n), (X - C (M i i))).degree < ↑(fintype.card n - 1) :=
begin
  rw [char_poly, det, ← insert_erase (mem_univ (equiv.refl n)),
    sum_insert (not_mem_erase (equiv.refl n) univ), add_comm],
  simp only [char_matrix_apply_eq, one_mul, equiv.perm.sign_refl, id.def, int.cast_one,
    units.coe_one, add_sub_cancel, equiv.coe_refl],
  rw ← mem_degree_lt, apply submodule.sum_mem (degree_lt R (fintype.card n - 1)),
  intros c hc, rw [← C_eq_int_cast, C_mul'],
  apply submodule.smul_mem (degree_lt R (fintype.card n - 1)) ↑↑(equiv.perm.sign c),
  rw mem_degree_lt, apply lt_of_le_of_lt degree_le_nat_degree _, rw with_bot.coe_lt_coe,
  apply lt_of_le_of_lt _ (equiv.perm.fixed_point_card_lt_of_ne_refl (ne_of_mem_erase hc)),
  apply le_trans (polynomial.nat_degree_prod_le univ (λ i : n, (char_matrix M (c i) i))) _,
  rw card_eq_sum_ones, rw sum_filter, apply sum_le_sum,
  intros, apply char_matrix_apply_nat_degree_le,
end

lemma char_poly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : fintype.card n - 1 ≤ k) :
  (char_poly M).coeff k = (∏ i : n, (X - C (M i i))).coeff k :=
begin
  apply eq_of_sub_eq_zero, rw ← coeff_sub, apply polynomial.coeff_eq_zero_of_degree_lt,
  apply lt_of_lt_of_le (char_poly_sub_diagonal_degree_lt M) _, rw with_bot.coe_le_coe, apply h,
end

lemma det_of_card_zero (h : fintype.card n = 0) (M : matrix n n R) : M.det = 1 :=
by { rw fintype.card_eq_zero_iff at h, suffices : M = 1, { simp [this] }, ext, tauto }


theorem char_poly_degree_eq_dim [nontrivial R] (M : matrix n n R) :
(char_poly M).degree = fintype.card n :=
begin
  by_cases fintype.card n = 0, rw h, unfold char_poly, rw det_of_card_zero, simpa,
  rw ← sub_add_cancel (char_poly M) (∏ (i : n), (X - C (M i i))),
  have h1 : (∏ (i : n), (X - C (M i i))).degree = fintype.card n,
  { rw degree_eq_iff_nat_degree_eq_of_pos, swap, apply nat.pos_of_ne_zero h,
    rw nat_degree_prod', simp_rw nat_degree_X_sub_C, unfold fintype.card, simp,
    simp_rw (monic_X_sub_C _).leading_coeff, simp, },
  rw degree_add_eq_of_degree_lt, exact h1, rw h1,
  apply lt_trans (char_poly_sub_diagonal_degree_lt M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

theorem char_poly_nat_degree_eq_dim [nontrivial R] (M : matrix n n R) :
  (char_poly M).nat_degree = fintype.card n :=
nat_degree_eq_of_degree_eq_some (degree_char_poly_eq_dim M)

lemma char_poly_monic_of_nontrivial [nontrivial R] (M : matrix n n R) :
  monic (char_poly M) :=
begin
  by_cases fintype.card n = 0, rw [char_poly, det_of_card_zero h], apply monic_one,
  have mon : (∏ (i : n), (X - C (M i i))).monic,
  { apply monic_prod_of_monic univ (λ i : n, (X - C (M i i))), simp [monic_X_sub_C], },
  rw ← sub_add_cancel (∏ (i : n), (X - C (M i i))) (char_poly M) at mon,
  rw monic at *, rw leading_coeff_add_of_degree_lt at mon, rw ← mon,
  rw degree_char_poly_eq_dim, rw ← neg_sub, rw degree_neg,
  apply lt_trans (char_poly_sub_diagonal_degree_lt M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

lemma char_poly_monic (M : matrix n n R) :
  monic (char_poly M) :=
begin
  classical, by_cases h : nontrivial R,
  { letI := h, apply char_poly_monic_of_nontrivial, },
  { rw nontrivial_iff at h, push_neg at h, apply h, }
end

theorem trace_eq_char_poly [nonempty n] (M : matrix n n R) :
  (matrix.trace n R R) M = -(char_poly M).coeff (fintype.card n - 1) :=
begin
  by_cases nontrivial R; try { rw not_nontrivial_iff_subsingleton at h }; haveI := h, swap,
  { apply subsingleton.elim },
  rw char_poly_coeff_eq_prod_coeff_of_le, swap, refl,
  rw [fintype.card, prod_X_sub_C_coeff_card_pred univ (λ i : n, M i i)], simp,
  rw [← fintype.card, fintype.card_pos_iff], apply_instance,
end

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map
lemma mat_poly_equiv_eval (M : matrix n n (polynomial R)) (r : R) (i j : n) :
  (mat_poly_equiv M).eval ((scalar n) r) i j = (M i j).eval r :=
begin
  unfold polynomial.eval, unfold eval₂,
  transitivity finsupp.sum (mat_poly_equiv M) (λ (e : ℕ) (a : matrix n n R),
    (a * (scalar n) r ^ e) i j),
  { unfold finsupp.sum, rw sum_apply, rw sum_apply, dsimp, refl, },
  { simp_rw ← (scalar n).map_pow, simp_rw ← (matrix.scalar.commute _ _).eq,
    simp only [coe_scalar, matrix.one_mul, ring_hom.id_apply,
      smul_val, mul_eq_mul, algebra.smul_mul_assoc],
    have h : ∀ x : ℕ, (λ (e : ℕ) (a : R), r ^ e * a) x 0 = 0 := by simp,
    symmetry, rw ← finsupp.sum_map_range_index h, swap, refl,
    refine congr (congr rfl _) (by {ext, rw mul_comm}), ext, rw finsupp.map_range_apply,
    simp [apply_eq_coeff], }
end

lemma eval_det (M : matrix n n (polynomial R)) (r : R) :
  polynomial.eval r M.det = (polynomial.eval (matrix.scalar n r) (mat_poly_equiv M)).det :=
begin
  rw [polynomial.eval, ← coe_eval₂_ring_hom, ring_hom.map_det],
  apply congr_arg det, ext, symmetry, convert mat_poly_equiv_eval _ _ _ _,
end

theorem det_eq_char_poly (M : matrix n n R) :
  M.det = (-1)^(fintype.card n) * (char_poly M).coeff 0:=
begin
  rw [coeff_zero_eq_eval_zero, char_poly, eval_det, mat_poly_equiv_char_matrix, ← det_smul],
  simp
end
