/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/

import algebra.polynomial.big_operators
import data.matrix.char_p
import field_theory.finite.basic
import group_theory.perm.cycles
import linear_algebra.charpoly.basic
import linear_algebra.matrix.trace
import ring_theory.polynomial.basic
import ring_theory.power_basis

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th coefficient of
  the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/

noncomputable theory

universes u v w z

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n G : Type v} [decidable_eq n] [fintype n]
variables {α β : Type v} [decidable_eq α]


open finset
open polynomial

variable {M : matrix n n R}

lemma charmatrix_apply_nat_degree [nontrivial R] (i j : n) :
  (charmatrix M i j).nat_degree = ite (i = j) 1 0 :=
by { by_cases i = j; simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (nat.succ_pos 0)], }

lemma charmatrix_apply_nat_degree_le (i j : n) :
  (charmatrix M i j).nat_degree ≤ ite (i = j) 1 0 :=
by split_ifs; simp [h, nat_degree_X_sub_C_le]

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
  (matrix.trace n R R) M = -M.charpoly.coeff (fintype.card n - 1) :=
begin
  nontriviality,
  rw charpoly_coeff_eq_prod_coeff_of_le, swap, refl,
  rw [fintype.card, prod_X_sub_C_coeff_card_pred univ (λ i : n, M i i)], simp,
  rw [← fintype.card, fintype.card_pos_iff], apply_instance,
end

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map
lemma mat_poly_equiv_eval (M : matrix n n (polynomial R)) (r : R) (i j : n) :
  (mat_poly_equiv M).eval ((scalar n) r) i j = (M i j).eval r :=
begin
  unfold polynomial.eval, unfold eval₂,
  transitivity polynomial.sum (mat_poly_equiv M) (λ (e : ℕ) (a : matrix n n R),
    (a * (scalar n) r ^ e) i j),
  { unfold polynomial.sum, rw matrix.sum_apply, dsimp, refl },
  { simp_rw [←ring_hom.map_pow, ←(matrix.scalar.commute _ _).eq],
    simp only [coe_scalar, matrix.one_mul, ring_hom.id_apply,
      pi.smul_apply, smul_eq_mul, mul_eq_mul, algebra.smul_mul_assoc],
    have h : ∀ x : ℕ, (λ (e : ℕ) (a : R), r ^ e * a) x 0 = 0 := by simp,
    simp only [polynomial.sum, mat_poly_equiv_coeff_apply, mul_comm],
    apply (finset.sum_subset (support_subset_support_mat_poly_equiv _ _ _) _).symm,
    assume n hn h'n,
    rw not_mem_support_iff at h'n,
    simp only [h'n, zero_mul] }
end

lemma eval_det (M : matrix n n (polynomial R)) (r : R) :
  polynomial.eval r M.det = (polynomial.eval (matrix.scalar n r) (mat_poly_equiv M)).det :=
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

variables {p : ℕ} [fact p.prime]

lemma mat_poly_equiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [field K] (M : matrix n n K) :
  mat_poly_equiv
      ((expand K (k) : polynomial K →+* polynomial K).map_matrix (charmatrix (M ^ k))) =
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

@[simp] lemma finite_field.charpoly_pow_card {K : Type*} [field K] [fintype K] (M : matrix n n K) :
  (M ^ (fintype.card K)).charpoly = M.charpoly :=
begin
  casesI (is_empty_or_nonempty n).symm,
  { cases char_p.exists K with p hp, letI := hp,
    rcases finite_field.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩,
    haveI : fact p.prime := ⟨hp⟩,
    dsimp at hk, rw hk at *,
    apply (frobenius_inj (polynomial K) p).iterate k,
    repeat { rw iterate_frobenius, rw ← hk },
    rw ← finite_field.expand_card,
    unfold charpoly, rw [alg_hom.map_det, ← coe_det_monoid_hom,
      ← (det_monoid_hom : matrix n n (polynomial K) →* polynomial K).map_pow],
    apply congr_arg det,
    refine mat_poly_equiv.injective _,
    rw [alg_equiv.map_pow, mat_poly_equiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow],
    { exact (id (mat_poly_equiv_eq_X_pow_sub_C (p ^ k) M) : _) },
    { exact (C M).commute_X } },
  { -- TODO[gh-6025]: remove this `haveI` once `subsingleton_of_empty_right` is a global instance
    haveI : subsingleton (matrix n n K) := matrix.subsingleton_of_empty_right,
    exact congr_arg _ (subsingleton.elim _ _), },
end

@[simp] lemma zmod.charpoly_pow_card (M : matrix n n (zmod p)) :
  (M ^ p).charpoly = M.charpoly :=
by { have h := finite_field.charpoly_pow_card M, rwa zmod.card at h, }

lemma finite_field.trace_pow_card {K : Type*} [field K] [fintype K] [nonempty n]
  (M : matrix n n K) : trace n K K (M ^ (fintype.card K)) = (trace n K K M) ^ (fintype.card K) :=
by rw [trace_eq_neg_charpoly_coeff, trace_eq_neg_charpoly_coeff,
       finite_field.charpoly_pow_card, finite_field.pow_card]

lemma zmod.trace_pow_card {p:ℕ} [fact p.prime] [nonempty n] (M : matrix n n (zmod p)) :
  trace n (zmod p) (zmod p) (M ^ p) = (trace n (zmod p) (zmod p) M)^p :=
by { have h := finite_field.trace_pow_card M, rwa zmod.card at h, }

namespace matrix

theorem is_integral : is_integral R M := ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type*} [field K] (M : matrix n n K) :
  (minpoly K M) ∣ M.charpoly :=
minpoly.dvd _ _ (aeval_self_charpoly M)

end matrix

section power_basis

open algebra

/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
lemma charpoly_left_mul_matrix {K S : Type*} [field K] [comm_ring S] [algebra K S]
  (h : power_basis K S) :
  (left_mul_matrix h.basis h.gen).charpoly = minpoly K h.gen :=
begin
  apply minpoly.unique,
  { apply charpoly_monic },
  { apply (left_mul_matrix _).injective_iff.mp (left_mul_matrix_injective h.basis),
    rw [← polynomial.aeval_alg_hom_apply, aeval_self_charpoly] },
  { intros q q_monic root_q,
    rw [charpoly_degree_eq_dim, fintype.card_fin, degree_eq_nat_degree q_monic.ne_zero],
    apply with_bot.some_le_some.mpr,
    exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q }
end

end power_basis
