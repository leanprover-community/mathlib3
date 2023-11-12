/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/

import data.polynomial.expand
import linear_algebra.matrix.charpoly.basic

/-!
# Characteristic polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/

noncomputable theory

universes u v w z

open polynomial matrix
open_locale big_operators polynomial

variables {R : Type u} [comm_ring R]
variables {n G : Type v} [decidable_eq n] [fintype n]
variables {α β : Type v} [decidable_eq α]


open finset

variable {M : matrix n n R}

lemma charmatrix_apply_nat_degree [nontrivial R] (i j : n) :
  (charmatrix M i j).nat_degree = ite (i = j) 1 0 :=
by { by_cases i = j; simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (nat.succ_pos 0)], }

lemma charmatrix_apply_nat_degree_le (i j : n) :
  (charmatrix M i j).nat_degree ≤ ite (i = j) 1 0 :=
by split_ifs; simp [h, nat_degree_X_sub_C_le]

namespace matrix

variable (M)
lemma charpoly_sub_diagonal_degree_lt :
(M.charpoly - ∏ (i : n), (X - C (M i i))).degree < ↑(fintype.card n - 1) :=
begin
  rw [charpoly, det_apply', ← insert_erase (mem_univ (equiv.refl n)),
    sum_insert (not_mem_erase (equiv.refl n) univ), add_comm],
  simp only [charmatrix_apply_eq, one_mul, equiv.perm.sign_refl, id.def, int.cast_one,
    units.coe_one, add_sub_cancel, equiv.coe_refl],
  rw ← mem_degree_lt, apply submodule.sum_mem (degree_lt R (fintype.card n - 1)),
  intros c hc, rw [← C_eq_int_cast, C_mul'],
  apply submodule.smul_mem (degree_lt R (fintype.card n - 1)) ↑↑(equiv.perm.sign c),
  rw mem_degree_lt, apply lt_of_le_of_lt degree_le_nat_degree _, rw with_bot.coe_lt_coe,
  apply lt_of_le_of_lt _ (equiv.perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc)),
  apply le_trans (polynomial.nat_degree_prod_le univ (λ i : n, (charmatrix M (c i) i))) _,
  rw card_eq_sum_ones, rw sum_filter, apply sum_le_sum,
  intros, apply charmatrix_apply_nat_degree_le,
end

lemma charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : fintype.card n - 1 ≤ k) :
  M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k :=
begin
  apply eq_of_sub_eq_zero, rw ← coeff_sub, apply polynomial.coeff_eq_zero_of_degree_lt,
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) _, rw with_bot.coe_le_coe, apply h,
end

lemma det_of_card_zero (h : fintype.card n = 0) (M : matrix n n R) : M.det = 1 :=
by { rw fintype.card_eq_zero_iff at h, suffices : M = 1, { simp [this] }, ext i, exact h.elim i }

theorem charpoly_degree_eq_dim [nontrivial R] (M : matrix n n R) :
M.charpoly.degree = fintype.card n :=
begin
  by_cases fintype.card n = 0,
  { rw h, unfold charpoly, rw det_of_card_zero, {simp}, {assumption} },
  rw ← sub_add_cancel M.charpoly (∏ (i : n), (X - C (M i i))),
  have h1 : (∏ (i : n), (X - C (M i i))).degree = fintype.card n,
  { rw degree_eq_iff_nat_degree_eq_of_pos, swap, apply nat.pos_of_ne_zero h,
    rw nat_degree_prod', simp_rw nat_degree_X_sub_C, unfold fintype.card, simp,
    simp_rw (monic_X_sub_C _).leading_coeff, simp, },
  rw degree_add_eq_right_of_degree_lt, exact h1, rw h1,
  apply lt_trans (charpoly_sub_diagonal_degree_lt M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

theorem charpoly_nat_degree_eq_dim [nontrivial R] (M : matrix n n R) :
  M.charpoly.nat_degree = fintype.card n :=
nat_degree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

lemma charpoly_monic (M : matrix n n R) : M.charpoly.monic :=
begin
  nontriviality,
  by_cases fintype.card n = 0, {rw [charpoly, det_of_card_zero h], apply monic_one},
  have mon : (∏ (i : n), (X - C (M i i))).monic,
  { apply monic_prod_of_monic univ (λ i : n, (X - C (M i i))), simp [monic_X_sub_C], },
  rw ← sub_add_cancel (∏ (i : n), (X - C (M i i))) M.charpoly at mon,
  rw monic at *, rw leading_coeff_add_of_degree_lt at mon, rw ← mon,
  rw charpoly_degree_eq_dim, rw ← neg_sub, rw degree_neg,
  apply lt_trans (charpoly_sub_diagonal_degree_lt M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

theorem trace_eq_neg_charpoly_coeff [nonempty n] (M : matrix n n R) :
  trace M = -M.charpoly.coeff (fintype.card n - 1) :=
begin
  rw charpoly_coeff_eq_prod_coeff_of_le, swap, refl,
  rw [fintype.card, prod_X_sub_C_coeff_card_pred univ (λ i : n, M i i) fintype.card_pos, neg_neg,
    trace],
  refl
end

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map
lemma mat_poly_equiv_eval (M : matrix n n R[X]) (r : R) (i j : n) :
  (mat_poly_equiv M).eval ((scalar n) r) i j = (M i j).eval r :=
begin
  unfold polynomial.eval, unfold eval₂,
  transitivity polynomial.sum (mat_poly_equiv M) (λ (e : ℕ) (a : matrix n n R),
    (a * (scalar n) r ^ e) i j),
  { unfold polynomial.sum, rw sum_apply, dsimp, refl },
  { simp_rw [←ring_hom.map_pow, ←(scalar.commute _ _).eq],
    simp only [coe_scalar, matrix.one_mul, ring_hom.id_apply,
      pi.smul_apply, smul_eq_mul, mul_eq_mul, algebra.smul_mul_assoc],
    have h : ∀ x : ℕ, (λ (e : ℕ) (a : R), r ^ e * a) x 0 = 0 := by simp,
    simp only [polynomial.sum, mat_poly_equiv_coeff_apply, mul_comm],
    apply (finset.sum_subset (support_subset_support_mat_poly_equiv _ _ _) _).symm,
    assume n hn h'n,
    rw not_mem_support_iff at h'n,
    simp only [h'n, zero_mul] }
end

lemma eval_det (M : matrix n n R[X]) (r : R) :
  polynomial.eval r M.det = (polynomial.eval (scalar n r) (mat_poly_equiv M)).det :=
begin
  rw [polynomial.eval, ← coe_eval₂_ring_hom, ring_hom.map_det],
  apply congr_arg det, ext, symmetry, convert mat_poly_equiv_eval _ _ _ _,
end

theorem det_eq_sign_charpoly_coeff (M : matrix n n R) :
  M.det = (-1)^(fintype.card n) * M.charpoly.coeff 0:=
begin
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, mat_poly_equiv_charmatrix, ← det_smul],
  simp
end

end matrix

variables {p : ℕ} [fact p.prime]

lemma mat_poly_equiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [field K] (M : matrix n n K) :
  mat_poly_equiv
      ((expand K (k) : K[X] →+* K[X]).map_matrix (charmatrix (M ^ k))) =
    X ^ k - C (M ^ k) :=
begin
  ext m,
  rw [coeff_sub, coeff_C, mat_poly_equiv_coeff_apply, ring_hom.map_matrix_apply, matrix.map_apply,
    alg_hom.coe_to_ring_hom, dmatrix.sub_apply, coeff_X_pow],
  by_cases hij : i = j,
  { rw [hij, charmatrix_apply_eq, alg_hom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow,
     coeff_C],
    split_ifs with mp m0;
    simp only [matrix.one_apply_eq, dmatrix.zero_apply] },
  { rw [charmatrix_apply_ne _ _ _ hij, alg_hom.map_neg, expand_C, coeff_neg, coeff_C],
    split_ifs with m0 mp;
    simp only [hij, zero_sub, dmatrix.zero_apply, sub_zero, neg_zero, matrix.one_apply_ne, ne.def,
      not_false_iff] }
end

namespace matrix

/-- Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; that is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix. -/
lemma aeval_eq_aeval_mod_charpoly (M : matrix n n R) (p : R[X]) :
  aeval M p = aeval M (p %ₘ M.charpoly) :=
(aeval_mod_by_monic_eq_self_of_root M.charpoly_monic M.aeval_self_charpoly).symm

/-- Any matrix power can be computed as the sum of matrix powers less than `fintype.card n`.

TODO: add the statement for negative powers phrased with `zpow`. -/
lemma pow_eq_aeval_mod_charpoly (M : matrix n n R) (k : ℕ) : M^k = aeval M (X^k %ₘ M.charpoly) :=
by rw [←aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

end matrix

section ideal

lemma coeff_charpoly_mem_ideal_pow {I : ideal R} (h : ∀ i j, M i j ∈ I) (k : ℕ) :
  M.charpoly.coeff k ∈ I ^ (fintype.card n - k) :=
begin
  delta charpoly,
  rw [matrix.det_apply, finset_sum_coeff],
  apply sum_mem,
  rintro c -,
  rw [coeff_smul, submodule.smul_mem_iff'],
  have : ∑ (x : n), 1 = fintype.card n := by rw [finset.sum_const, card_univ, smul_eq_mul, mul_one],
  rw ← this,
  apply coeff_prod_mem_ideal_pow_tsub,
  rintro i - (_|k),
  { rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, coeff_X_mul_zero, coeff_C_zero, zero_sub,
      neg_mem_iff],
    exact h (c i) i },
  { rw [nat.succ_eq_one_add, tsub_self_add, pow_zero, ideal.one_eq_top],
    exact submodule.mem_top }
end

end ideal
