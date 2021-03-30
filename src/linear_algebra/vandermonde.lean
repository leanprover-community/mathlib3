/-
Copyright (c) 2021 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
import linear_algebra.matrix
import algebra.geom_sum

/-!
# Formula for the determinent of a Vandermonde matrix.

## Theorems

1. `vandermonde_det` gives the formula for the determinant of a Vandermonde matrix.

## Implementation details

The proof proceeds by three transformations of the matrix, each accomplished but multiplying by a
matrix whose determinant can easily be written down. Transformation 1 is to subtract the first row
from each of the others. This is multiplication by `vandermonde_step1_op`. After this
transformation every entry below row one is the difference between two `i`th powers and allows us to
factor `a i - a 0` from each row (except the first). This is multiplication by a diagonal matrix.
The final step is to add the right multiples of each column to earlier columns in order to rewrite
the matrix so the first minor is just a smaller Vandermonde matrix. This is multiplication by
`vandermonde_step3_op`. The result now follows by induction.
-/

noncomputable theory
open_locale classical

universes u v
variables (R : Type u) [comm_ring R] (n : ℕ) (a : ℕ → R)

open int equiv equiv.perm finset fintype
open_locale big_operators

namespace matrix

/-- Definition of a Vandermonde matrix -/
def vandermonde : matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j, (a i) ^ (j : ℕ)

@[simp] lemma vandermonde_def (i j : fin (n + 1)) :
  vandermonde R n a i j = (a i) ^ (j : ℕ) := rfl

/-- The Vandermonde matrix after the step 1 transformation -/
def vandermonde_step1 : matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j, if i = 0 then (a 0) ^ (j : ℕ) else (a i) ^ (j : ℕ) - (a 0) ^ (j : ℕ)

@[simp] lemma vandermonde_step1_row_eq_zero_def (j : fin (n + 1)) :
  vandermonde_step1 R n a 0 j = (a 0) ^ (j : ℕ) := rfl

@[simp] lemma vandermonde_step1_row_ne_zero_def (i j : fin (n + 1)) (h : i ≠ 0) :
  vandermonde_step1 R n a i j = (a i) ^ (↑j : ℕ) - (a 0) ^ (↑j : ℕ) := id (if_neg h)

/-- The matrix defining the step 1 transformation -/
def vandermonde_step1_op : matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j, if j = 0 then
  if i = 0 then 1 else -1
  else if i = j then 1 else 0

@[simp] lemma vandermonde_step1_op_diagonal_def (i : fin (n + 1)) :
  vandermonde_step1_op R n i i = 1 :=
begin
  dunfold vandermonde_step1_op,
  by_cases hi : i = 0,
  { rw [if_pos hi, if_pos hi] },
  { rw if_neg hi,
    exact if_pos rfl}
end

lemma vandermonde_step1_op_det : det (vandermonde_step1_op R n) = 1 :=
begin
  have h : ∀ (i j : fin (n + 1)), i < j → (vandermonde_step1_op R n) i j = 0,
  { intros i j hij,
    by_cases hj : j = 0,
    { have hh : i < 0, { rw hj at hij, exact hij },
      apply absurd hh not_lt_bot },
    { dunfold vandermonde_step1_op,
      rw if_neg hj,
      apply if_neg (ne_of_lt hij) }},
  rw det_of_lower_triangular _ h,
  apply fintype.prod_eq_one,
  simp
end

lemma vandermonde_step1_det : (vandermonde R n a).det = (vandermonde_step1 R n a).det :=
begin
  have h : vandermonde_step1 R n a = (vandermonde_step1_op R n) * (vandermonde R n a),
  { ext i k,
    rw [mul_eq_mul, mul_apply],
    by_cases hi : i = 0,
    { rw hi,
      have hj : ∀ j ≠ 0, vandermonde_step1_op R n 0 j * vandermonde R n a j k = 0,
      { intros j hj,
        dunfold vandermonde_step1_op,
        rw [if_neg hj, if_neg (ne.symm hj), zero_mul] },
      rw fintype.sum_eq_single 0 hj,
      simp },
    { have hj : ∀ j, j ≠ 0 ∧ j ≠ i → vandermonde_step1_op R n i j * vandermonde R n a j k = 0,
      { intros j h2,
        dunfold vandermonde_step1_op,
        rw [if_neg (h2.left), if_neg (ne.symm h2.right), zero_mul] },
      rw sum_eq_add _ _ (ne.symm hi) hj,
      simp [vandermonde_step1_op, vandermonde_step1, if_neg hi, sub_eq_neg_add] }},
  rw [h, mul_eq_mul, det_mul, vandermonde_step1_op_det, one_mul]
end

/-- The Vandermonde matrix after the step 2 transformation -/
def vandermonde_step2 : matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j, if i = 0 then (a 0) ^ (j : ℕ) else geom_sum₂ (a i) (a 0) (j : ℕ)

lemma vandermonde_step2_det :
  (vandermonde R n a).det =
    (∏ i in range n, (a (i + 1) - a 0)) * (vandermonde_step2 R n a).det :=
begin
  let d : fin (n + 1) → R := λ i, if ↑i = 0 then 1 else (a i) - (a 0),
  have h : vandermonde_step1 R n a = (diagonal d) * (vandermonde_step2 R n a),
  { ext,
    rw [mul_eq_mul, diagonal_mul],
    simp only [vandermonde_step1, vandermonde_step2, one_mul, ite_mul],
    by_cases h0 : i = 0,
    { have h0' : ↑i = 0 := fin.veq_of_eq h0,
      rw [if_pos h0, if_pos h0', if_pos h0] },
    { have h0' : ↑i ≠ 0 := (λ h, h0 (fin.eq_of_veq h)),
      rw [if_neg h0, if_neg h0', if_neg h0, mul_comm],
      exact (geom_sum₂_mul _ _ _).symm }},
  rw [vandermonde_step1_det, h, mul_eq_mul, det_mul],
  refine congr_fun (congr_arg has_mul.mul _) (vandermonde_step2 R n a).det,
  rw [det_diagonal, @fin.prod_univ_eq_prod_range R _ (λ i, ite ((i : ℕ) = 0) 1 (a i - a 0)),
    prod_range_succ'],
  simp
end

/-- The Vandermonde matrix after the step 3 transformation -/
def vandermonde_step3 :
  matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j,
  if i = 0 then if j = 0 then 1 else 0
  else if j = 0 then 0 else (a i) ^ (↑j - 1)

/-- The matrix defining the step 3 transformation -/
def vandermonde_step3_op : matrix (fin (n + 1)) (fin (n + 1)) R :=
λ i j, if i = j then 1 else
  if ↑j = ↑i + 1 then -(a 0) else 0

@[simp] lemma vandermonde_step3_op_diagonal (i : fin (n + 1)) :
  vandermonde_step3_op R n a i i = 1 := if_pos rfl

lemma vandermonde_step3_op_det : (vandermonde_step3_op R n a).det = 1 :=
begin
  have h : ∀ (i j : fin (n + 1)), j < i → (vandermonde_step3_op R n a) i j = 0,
  { intros i j hij,
    dunfold vandermonde_step3_op,
    rw if_neg (ne.symm (ne_of_lt hij)).elim,
    apply if_neg,
    intro hij',
    change ↑j < ↑i at hij,
    rw hij' at hij,
    exact nat.not_succ_lt_self hij },
  rw det_of_upper_triangular _ h,
  apply fintype.prod_eq_one,
  simp
end

lemma vandermonde_step3_det : (vandermonde_step2 R n a).det = (vandermonde_step3 R n a).det :=
begin
  rw [←mul_one (vandermonde_step2 R n a).det, ←vandermonde_step3_op_det R n a, ←det_mul],
  congr,
  ext i k,
  rw mul_apply,
  by_cases hk : k = 0,
  { rw hk,
    have hj : ∀ j ≠ 0, vandermonde_step2 R n a i j * vandermonde_step3_op R n a j 0 = 0,
    { intros j hj0,
      dunfold vandermonde_step3_op,
      rw [if_neg hj0, if_neg, mul_zero],
      exact (nat.succ_ne_zero ↑j).symm },
    rw fintype.sum_eq_single 0 hj,
    simp only [mul_one, vandermonde_step3_op_diagonal, vandermonde_step2, vandermonde_step3],
    by_cases hi : i = 0,
    { rw [if_pos hi, if_pos hi],
      simp only [fin.coe_zero, if_true, eq_self_iff_true, pow_zero] },
    { rw [if_neg hi, if_neg hi],
      simp only [geom_sum₂_zero, fin.coe_zero, if_true, eq_self_iff_true] }},
  { have hk1 : 1 ≤ ↑k := nat.pos_of_ne_zero (@fin.vne_of_ne _ k 0 hk),
    have hkmp : ↑k - 1 + 1 = ↑k := nat.sub_add_cancel hk1,
    have hk1' : ↑(k - 1) = ↑k - 1,
    { cases n,
      { exact absurd (fin.eq_zero k) hk },
      { rw [fin.coe_sub_of_le, fin.coe_one],
        exact hk1 }},
    have hk1k : ¬(k - 1) = k,
    { apply fin.ne_of_vne,
      rw [fin.val_eq_coe, hk1'],
      exact λ h, k.val.succ_ne_self.symm ((nat.sub_eq_iff_eq_add hk1).mp h) },
    have hj : ∀ j,
      j ≠ (k - 1) ∧ (j ≠ k) → vandermonde_step2 R n a i j * vandermonde_step3_op R n a j k = 0,
    { intros j h2,
      dunfold vandermonde_step3_op,
      rw if_neg h2.right,
      have hjk : ¬↑k = ↑j + 1,
      { apply mt (nat.sub_eq_iff_eq_add hk1).mpr,
        rw ←hk1',
        exact (fin.vne_of_ne h2.left).symm },
      rw [if_neg hjk, mul_zero] },
    rw sum_eq_add (k-1) k hk1k hj,
    { simp only [vandermonde_step2, vandermonde_step3, vandermonde_step3_op],
      rw [if_neg hk, if_neg hk1k, if_pos rfl, if_neg hk, hk1', hkmp, if_pos rfl],
      by_cases hi : i = 0,
      { rw [if_pos hi, if_pos hi, if_pos hi, mul_comm, ←neg_mul_eq_neg_mul,
          (pow_succ _ _).symm, hkmp, mul_one, add_left_neg] },
      { rw [if_neg hi, if_neg hi, if_neg hi, mul_one, mul_comm, ←neg_mul_eq_neg_mul],
        nth_rewrite 1 ←hkmp,
        rw geom_sum₂_succ_eq,
        ring }}},
end

lemma fin_one_sum_fin_congr_equiv_symm_apply_right {j : fin (n + 1)} (h : j ≠ 0) :
  (fin_sum_fin_equiv.trans (fin_congr (add_comm 1 n))).symm j = sum.inr (j.pred h) :=
begin
  simp only [fin_congr_symm, symm_trans_apply],
  erw fin_congr_apply_mk (add_comm n 1) _ j.2,
  rw fin_sum_fin_equiv_symm_apply_right,
  { simp only [],
    apply fin.eq_of_veq,
    simp only [fin.val_eq_coe, fin.coe_pred] },
  { exact nat.pos_of_ne_zero (λ hj, h (fin.eq_of_veq hj)) }
end

lemma vandermonde_step3_det' :
  (vandermonde_step3 R n.succ a).det = (vandermonde R n (λ i, a (i + 1))).det :=
begin
  transitivity
    (matrix.from_blocks (1 : matrix (fin 1) (fin 1) R) 0 0 (vandermonde R n (λ i, a (i + 1)))).det,
  { convert det_reindex_self' (equiv.trans fin_sum_fin_equiv (fin_congr (add_comm 1 (n + 1))))
      (matrix.from_blocks (1 : matrix (fin 1) (fin 1) R) 0 0 (vandermonde R n (λ i, a (i + 1)))),
    dunfold vandermonde_step3,
    ext i j,
    by_cases hi : i = 0,
    { rw hi,
      by_cases hj : j = 0,
      { simp [hj] },
      { rw [if_neg hj, fin_one_sum_fin_congr_equiv_symm_apply_right _ hj],
        simp }},
    { rw [if_neg hi, fin_one_sum_fin_congr_equiv_symm_apply_right _ hi],
      by_cases hj : j = 0,
      { rw hj,
        simp },
      { rw [if_neg hj, fin_one_sum_fin_congr_equiv_symm_apply_right _ hj,
          from_blocks_apply₂₂, vandermonde_def, fin.coe_pred _ hi, fin.coe_pred _ hj,
          nat.sub_add_cancel],
        exact nat.pos_of_ne_zero (λ hi', hi (fin.eq_of_veq hi')) }}},
  rw upper_two_block_triangular_det,
  simp
end

lemma vandermonde_det :
  det (vandermonde R n a) = ∏ i in range (n + 1), ∏ j in range i, ((a i) - (a j)) :=
begin
  induction n with n hn generalizing a,
  { simp },
  { rw [vandermonde_step2_det, vandermonde_step3_det, vandermonde_step3_det',
      hn (λ (i : ℕ), a (i + 1))],
    simp only [],
    nth_rewrite 2 prod_range_succ',
    rw [range_zero, finset.prod_empty, mul_one],
    have hr : ∀ (k : ℕ), ∏ (j : ℕ) in range (k + 1), (a (k + 1) - a j) =
      (∏ (j : ℕ) in range k, (a (k + 1) - a (j + 1))) * (a (k + 1) - a 0),
    { intro k, apply prod_range_succ' },
    simp_rw hr,
    rw [prod_mul_distrib, mul_comm] }
end

end matrix
