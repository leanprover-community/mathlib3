/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark.
-/

import linear_algebra.char_poly
import linear_algebra.matrix
import ring_theory.polynomial.basic
import data.zmod.basic
import number_theory.quadratic_reciprocity
import algebra.polynomial.big_operators
import field_theory.separable

noncomputable theory


universes u_1 u_2 u_3 u_4

open polynomial matrix
open_locale big_operators

variables {R : Type u_1} [comm_ring R]
variables {n : Type u_2} [fintype n] [decidable_eq n]
variables {α : Type u_2} [decidable_eq α]

open finset
open polynomial

section fixed_points

lemma gt_one_nonfixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
1 < (filter (λ (x : n), ¬ σ x = x) univ).card :=
begin
  rw one_lt_card_iff,
  contrapose! h, ext, dsimp,
  have := h (σ x) x, simp only [true_and, mem_filter, equiv.apply_eq_iff_eq, mem_univ, ne.def] at this,
  tauto,
end

lemma lt_card_sub_one_fixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
(filter (λ (x : n), σ x = x) univ).card < fintype.card n - 1:=
begin
  have hun := @filter_union_filter_neg_eq _ (λ (x : n), σ x = x) _ _ _ univ,
  have hin : (filter (λ (x : n), σ x = x) univ) ∩ (filter (λ (x : n), ¬ σ x = x) univ) = ∅
    := filter_inter_filter_neg_eq univ,
  rw ← disjoint_iff_inter_eq_empty at hin,
  rw fintype.card, conv_rhs { rw ← hun },
  rw card_disjoint_union hin,
  have := gt_one_nonfixed_point_of_nonrefl h, omega,
end

end fixed_points

variable {M : matrix n n R}

lemma nat_degree_char_matrix_val [nontrivial R] (i j : n) :
  (char_matrix M i j).nat_degree = ite (i = j) 1 0 :=
by { by_cases i = j, simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (nat.succ_pos 0)], simp [h], }

lemma nat_degree_char_matrix_val_le (i j : n) :
  (char_matrix M i j).nat_degree ≤ ite (i = j) 1 0 :=
begin
  by_cases i = j, swap, simp [h],
  rw [if_pos h, h, char_matrix_apply_eq], apply nat_degree_X_sub_C_le,
end

variable (M)
lemma low_degree_char_poly_sub_diagonal :
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
  apply lt_of_le_of_lt _ (lt_card_sub_one_fixed_point_of_nonrefl (ne_of_mem_erase hc)),
  apply le_trans (polynomial.nat_degree_prod_le univ (λ i : n, (char_matrix M (c i) i))) _,
  rw card_eq_sum_ones, rw sum_filter, apply sum_le_sum,
  intros, apply nat_degree_char_matrix_val_le,
end

lemma high_coeff_char_poly_eq_coeff_prod_diag {k : ℕ} (h : fintype.card n - 1 ≤ k) :
  (char_poly M).coeff k = (univ.prod (λ (i : n), X - C (M i i))).coeff k :=
begin
  apply eq_of_sub_eq_zero, rw ← coeff_sub, apply polynomial.coeff_eq_zero_of_degree_lt,
  apply lt_of_lt_of_le (low_degree_char_poly_sub_diagonal M) _, rw with_bot.coe_le_coe, apply h,
end

lemma det_of_dim_zero (h : fintype.card n = 0) (M : matrix n n R) : M.det = 1 :=
begin
  rw fintype.card_eq_zero_iff at h,
  have hone : M = 1, ext, exfalso, apply h i, rw hone, simp,
end

theorem degree_char_poly_eq_dim [nontrivial R] (M: matrix n n R) :
(char_poly M).degree = fintype.card n :=
begin
  by_cases fintype.card n = 0, rw h, unfold char_poly, rw det_of_dim_zero, simpa,
  rw ← sub_add_cancel (char_poly M) (∏ (i : n), (X - C (M i i))),
  have h1 : (∏ (i : n), (X - C (M i i))).degree = fintype.card n,
  { rw degree_eq_iff_nat_degree_eq_of_pos, swap, apply nat.pos_of_ne_zero h,
    rw nat_degree_prod', simp_rw nat_degree_X_sub_C, unfold fintype.card, simp,
    simp_rw (monic_X_sub_C _).leading_coeff, simp, },
  rw degree_add_eq_of_degree_lt, exact h1, rw h1,
  apply lt_trans (low_degree_char_poly_sub_diagonal M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

theorem nat_degree_char_poly_eq_dim [nontrivial R] (M: matrix n n R) :
  (char_poly M).nat_degree = fintype.card n :=
nat_degree_eq_of_degree_eq_some (degree_char_poly_eq_dim M)

lemma char_poly_monic_of_nontrivial [nontrivial R] (M : matrix n n R):
  monic (char_poly M):=
begin
  by_cases fintype.card n = 0, rw [char_poly, det_of_dim_zero h], apply monic_one,
  have mon : (∏ (i : n), (X - C (M i i))).monic,
  { apply monic_prod_of_monic univ (λ i : n, (X - C (M i i))), simp [monic_X_sub_C], },
  rw ← sub_add_cancel (∏ (i : n), (X - C (M i i))) (char_poly M) at mon,
  rw monic at *, rw leading_coeff_add_of_degree_lt at mon, rw ← mon,
  rw degree_char_poly_eq_dim, rw ← neg_sub, rw degree_neg,
  apply lt_trans (low_degree_char_poly_sub_diagonal M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

lemma char_poly_monic (M : matrix n n R):
  monic (char_poly M):=
begin
  classical,
  by_cases h : nontrivial R,
  { apply @char_poly_monic_of_nontrivial _ _ _ _ _ h, },
  { unfold monic, rw nontrivial_iff at h, push_neg at h, apply h, }
end

--shouldn't need these instances, but might need casework
theorem trace_from_char_poly [nontrivial R] [inhabited n] (M: matrix n n R) :
(matrix.trace n R R) M = -(char_poly M).coeff (fintype.card n - 1) :=
begin
  rw high_coeff_char_poly_eq_coeff_prod_diag, swap, refl,
  rw [fintype.card, prod_X_sub_C_coeff_card_pred univ (λ i : n, M i i)], simp,
  rw [← fintype.card, fintype.card_pos_iff], apply_instance,
end

lemma ring_hom_det {S : Type u_1} [comm_ring S] {M : matrix n n R} {f : R →+* S} :
  f M.det = matrix.det (f.map_matrix M) :=
by { unfold matrix.det, simp [f.map_sum, f.map_prod] }

lemma alg_hom_det {S : Type u_1} [comm_ring S] [algebra R S] {T : Type u_1} [comm_ring T] [algebra R T]
  {M : matrix n n S} {f : S →ₐ[R] T} :
  f M.det = matrix.det ((f : S →+* T).map_matrix M) :=
by { rw [← alg_hom.coe_to_ring_hom, ring_hom_det], }

lemma matrix.scalar.commute (r : R) (M : matrix n n R) : commute (scalar n r) M :=
by { unfold commute, unfold semiconj_by, simp }

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map
lemma eval_mat_poly_equiv (M : matrix n n (polynomial R)) (r : R) (i j : n) :
  polynomial.eval r (M i j) = polynomial.eval ((scalar n) r) (mat_poly_equiv M) i j :=
begin
  unfold polynomial.eval, unfold eval₂,
  transitivity finsupp.sum (mat_poly_equiv M) (λ (e : ℕ) (a : matrix n n R),
    (a * (scalar n) r ^ e) i j),
  { simp_rw ← (scalar n).map_pow, simp_rw ← (matrix.scalar.commute _ _).eq,
    simp only [coe_scalar, matrix.one_mul, ring_hom.id_apply,
      smul_val, mul_eq_mul, algebra.smul_mul_assoc],
    have h : ∀ x : ℕ, (λ (e : ℕ) (a : R), r ^ e * a) x 0 = 0 := by simp,
    rw ← finsupp.sum_map_range_index h, swap, refl,
    refine congr (congr rfl _) (by {ext, rw mul_comm}), ext, rw finsupp.map_range_apply,
    simp [apply_eq_coeff], },
  { unfold finsupp.sum, rw sum_apply, rw sum_apply, dsimp, refl, }
end

lemma eval_det (M : matrix n n (polynomial R)) (r : R) :
  polynomial.eval r M.det = (polynomial.eval (matrix.scalar n r) (mat_poly_equiv M)).det :=
begin
  rw [polynomial.eval, ← coe_eval₂_ring_hom, ring_hom_det], refine congr rfl _,
  rw [ring_hom.map_matrix_apply, coe_eval₂_ring_hom, ← polynomial.eval],
  ext, apply eval_mat_poly_equiv,
end

theorem det_from_char_poly (M: matrix n n R) :
M.det = (-1)^(fintype.card n) * (char_poly M).coeff 0:=
begin
  rw [coeff_zero_eq_eval_zero, char_poly, eval_det, mat_poly_equiv_char_matrix, ← det_smul],
  simp
end

section char_p

lemma matrix.scalar_inj [inhabited n] {r s : R} : scalar n r = scalar n s ↔ r = s :=
begin
  split; intro h, rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h],
  rw h,
end

instance matrix.char_p [inhabited n] (p : ℕ) [char_p R p] : char_p (matrix n n R) p :=
{ cast_eq_zero_iff :=
  begin
    intro k, rw ← char_p.cast_eq_zero_iff R p k,
    rw ← nat.cast_zero, repeat {rw ← (scalar n).map_nat_cast},
    rw matrix.scalar_inj, refl,
  end }

lemma det_pow (k : ℕ) (M : matrix n n R) :
(M ^ k).det = (M.det) ^ k :=
begin
  induction k with k hk, simp,
  repeat {rw pow_succ}, rw ← hk, squeeze_simp,
end


--lemma comp_det (p : polynomial R) (M : matrix n n (polynomial R)) :
--  (M.det).comp p = matrix.det (λ i j : n, (M i j).comp p) :=
--by { unfold comp, rw ← coe_eval₂_ring_hom, rw ring_hom_det }

variables (p : ℕ) [fact p.prime]

lemma frobenius_fixed (a : zmod p): a ^ p = a :=
begin
  have posp : 0 < p, { apply nat.prime.pos, assumption, },
  by_cases a = 0, rw h, rw zero_pow posp,
  conv_rhs {rw ← one_mul a, rw ← pow_one a}, rw ← zmod.fermat_little p h,
  rw ← pow_add, refine congr rfl _, symmetry, apply nat.succ_pred_eq_of_pos posp,
end

lemma zmod.expand_p (f : polynomial (zmod p)) :
expand (zmod p) p f = f ^ p :=
begin
  apply f.induction_on', intros a b ha hb, rw add_pow_char, simp [ha, hb], assumption,
  intros n a, rw polynomial.expand_monomial, repeat {rw single_eq_C_mul_X},
  rw [mul_pow, ← C.map_pow, frobenius_fixed p a], ring_exp,
end


@[simp]
lemma empty_matrix_eq_zero {R : Type*} [ring R] (hn : ¬ nonempty n) (M : matrix n n R) :
M = 0 :=
begin
  ext, contrapose! hn, use i,
end

theorem sub_pow_char_of_commute (R : Type u_1) [ring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) (h : commute x y):
(x - y)^p = x^p - y^p :=
begin
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute], simp,
  unfold commute, unfold semiconj_by, rw [sub_mul, mul_sub, h.eq],
end

#check matrix.mul_eq_mul
#check monoid.pow
#check @matrix.monoid

@[simp] theorem matrix.pow_eq_pow [semiring α] (M : matrix n n α) (k : ℕ) :
  M ^ k = monoid.pow M k :=
begin
  induction k with d hd, refl,
  rw [pow_succ, hd, mul_eq_mul], refl,
end

#check matrix.monoid

lemma char_poly_pow_p_char_p (M : matrix n n (zmod p)) :
char_poly (M ^ p) = char_poly M :=
begin
  classical,
  by_cases hn : nonempty n, letI := hn, haveI : inhabited n := by { inhabit n, assumption },
  clear _inst_1 hn,
  swap, { congr, rw empty_matrix_eq_zero hn M, apply empty_matrix_eq_zero hn },

  apply frobenius_inj (polynomial (zmod p)) p, repeat {rw frobenius_def},
  rw ← zmod.expand_p,
  unfold char_poly, rw alg_hom_det, rw ← det_pow, simp,
  congr,
  unfold char_matrix,
  transitivity ((scalar n) X - C.map_matrix M) ^ p, simp,
  rw sub_pow_char_of_commute,
  swap, { apply matrix.scalar.commute },
  -- convert sub_pow_char_of_commute _,
  -- rw sub_pow_char_of_commute,
  -- rw ← map_pow,
  -- rw ← C.map_matrix.map_pow, rw ← (scalar n).map_pow,
  -- ext, refine congr (congr rfl _) rfl, by_cases i = j; simp [h], sorry,
  -- {
  --   refine congr rfl _, refine congr (congr _ rfl) rfl,
  --   refine congr (congr _ rfl) rfl, sorry,
  -- }
end

end char_p
