/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import group_theory.perm.fin
import linear_algebra.determinant
import tactic.ring_exp

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

open equiv

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

lemma succ_above_cycle_range {n : ℕ} (i j : fin n) :
  i.succ.succ_above (i.cycle_range j) = swap 0 i.succ j.succ :=
begin
  cases n,
  { rcases j with ⟨_, ⟨⟩⟩ },
  rcases lt_trichotomy j i with hlt | heq | hgt,
  { rw [fin.cycle_range_of_lt hlt, fin.succ_above_below, swap_apply_of_ne_of_ne],
    { ext, simp [fin.coe_add_one (lt_of_lt_of_le hlt (nat.lt_succ_iff.mp i.2))] },
    { apply fin.succ_ne_zero },
    { exact (fin.succ_injective _).ne hlt.ne },
    { rw fin.lt_iff_coe_lt_coe,
      simpa [fin.coe_add_one (lt_of_lt_of_le hlt (nat.lt_succ_iff.mp i.2))] using hlt } },
  { rw [heq, fin.cycle_range_self, fin.succ_above_below, swap_apply_right, fin.cast_succ_zero],
    { rw fin.cast_succ_zero, apply fin.succ_pos } },
  { rw [fin.cycle_range_of_gt hgt, fin.succ_above_above, swap_apply_of_ne_of_ne],
    { apply fin.succ_ne_zero },
    { apply (fin.succ_injective _).ne hgt.ne.symm },
    { simpa [fin.le_iff_coe_le_coe] using hgt } },
end

/-- Develop the determinant of an `n+1 × n+1` matrix along the first row. -/
lemma det_succ_row {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) :
  det A = ∑ i : fin n.succ, (-1) ^ (i : ℕ) * A i 0 *
    det (λ (i' j' : fin n), A (i.succ_above i') j'.succ) :=
begin
  rw [matrix.det_apply, finset.univ_perm_fin_succ, ← finset.univ_product_univ],
  simp only [finset.sum_map, equiv.to_embedding_apply, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, fin.cases _ (λ i, _) i),
  { simp only [fin.prod_univ_succ, matrix.det_apply, finset.mul_sum,
        equiv.perm.decompose_fin_symm_apply_zero, fin.coe_zero, one_mul,
        equiv.perm.decompose_fin.symm_sign, equiv.swap_self, if_true, id.def, eq_self_iff_true,
        equiv.perm.decompose_fin_symm_apply_succ, fin.succ_above_zero, equiv.coe_refl, pow_zero,
        algebra.mul_smul_comm] },
  -- `univ_perm_fin_succ` gives a different embedding of `perm (fin n)` into
  -- `perm (fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = i.cycle_range.sign,
  { simp [fin.sign_cycle_range] },
  rw [fin.coe_succ, pow_succ, this, mul_assoc, mul_assoc, mul_left_comm ↑(equiv.perm.sign _),
      ← det_permute, matrix.det_apply, finset.mul_sum, finset.mul_sum],
  -- now we just need to move the crresponding parts to the same place
  refine finset.sum_congr rfl (λ σ _, _),
  rw [equiv.perm.decompose_fin.symm_sign, if_neg (fin.succ_ne_zero i)],
  calc ((-1) * σ.sign : ℤ) • ∏ i', A (equiv.perm.decompose_fin.symm (fin.succ i, σ) i') i'
      = ((-1) * σ.sign : ℤ) • (A (fin.succ i) 0 *
        ∏ i', A (((fin.succ i).succ_above) (fin.cycle_range i (σ i'))) i'.succ) : _
  ... = (-1) * (A (fin.succ i) 0 * (σ.sign : ℤ) •
        ∏ i', A (((fin.succ i).succ_above) (fin.cycle_range i (σ i'))) i'.succ) : by simp,
  simp only [fin.prod_univ_succ, succ_above_cycle_range,
    equiv.perm.decompose_fin_symm_apply_zero, equiv.perm.decompose_fin_symm_apply_succ]
end

/-- Develop the determinant of an `n+1 × n+1` matrix along the first column -/
lemma det_succ_column {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) :
  det A = ∑ j : fin n.succ, (-1) ^ (j : ℕ) * A 0 j *
    det (λ (i' j' : fin n), A i'.succ (j.succ_above j')) :=
by { rw [← det_transpose A, det_succ_row],
     refine finset.sum_congr rfl (λ i _, _),
     rw [← det_transpose],
     simp only [matrix.transpose_apply],
     refl }

lemma det_mul_row {n : Type*} [fintype n] [decidable_eq n] (v : n → R) (A : matrix n n R) :
  det (λ i j, v j * A i j) = (∏ i, v i) * det A :=
calc det (λ i j, v j * A i j) = det (A ⬝ diagonal v) :
  congr_arg det $ by { ext, simp [mul_comm] }
... = (∏ i, v i) * det A : by rw [det_mul, det_diagonal, mul_comm]

lemma det_mul_column {n : Type*} [fintype n] [decidable_eq n] (v : n → R) (A : matrix n n R) :
  det (λ i j, v i * A i j) = (∏ i, v i) * det A :=
calc det (λ i j, v i * A i j) = det (diagonal v ⬝ A) :
  congr_arg det $ by { ext, simp }
... = (∏ i, v i) * det A : by rw [det_mul, det_diagonal]

@[simp]
lemma fin.univ_filter_zero_lt {n : ℕ} :
  (finset.univ : finset (fin n.succ)).filter (λ i, 0 < i) =
    finset.univ.map ⟨fin.succ, fin.succ_injective _⟩ :=
begin
  ext i,
  simp only [finset.mem_filter, finset.mem_map, finset.mem_univ, true_and,
    function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine fin.cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i _, exact ⟨i, finset.mem_univ _, rfl⟩ } },
  { rintro ⟨i, _, rfl⟩,
    exact fin.succ_pos _ },
end

@[simp]
lemma fin.univ_filter_succ_lt {n : ℕ} (j : fin n) :
  (finset.univ : finset (fin n.succ)).filter (λ i, j.succ < i) =
    (finset.univ.filter (λ i, j < i)).map ⟨fin.succ, fin.succ_injective _⟩ :=
begin
  ext i,
  simp only [finset.mem_filter, finset.mem_map, finset.mem_univ, true_and,
      function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine fin.cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i hi,
      exact ⟨i, finset.mem_filter.mpr ⟨finset.mem_univ _, fin.succ_lt_succ_iff.mp hi⟩, rfl⟩ } },
  { rintro ⟨i, hi, rfl⟩,
    exact fin.succ_lt_succ_iff.mpr (finset.mem_filter.mp hi).2 },
end

-- `to_additive` version of `prod_filter_zero_lt, can't be autogenerated because
-- of the `0` in the statement
lemma sum_filter_zero_lt {M : Type*} [add_comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∑ i in finset.univ.filter (λ (i : fin n.succ), 0 < i), v i = ∑ (j : fin n), v j.succ :=
by rw [fin.univ_filter_zero_lt, finset.sum_map, function.embedding.coe_fn_mk]

@[to_additive]
lemma prod_filter_zero_lt {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in finset.univ.filter (λ (i : fin n.succ), 0 < i), v i = ∏ (j : fin n), v j.succ :=
by rw [fin.univ_filter_zero_lt, finset.prod_map, function.embedding.coe_fn_mk]

@[to_additive]
lemma prod_filter_succ_lt {M : Type*} [comm_monoid M] {n : ℕ} (j : fin n) (v : fin n.succ → M) :
  ∏ i in finset.univ.filter (λ i, j.succ < i), v i =
    ∏ j in finset.univ.filter (λ i, j < i), v j.succ :=
by rw [fin.univ_filter_succ_lt, finset.prod_map, function.embedding.coe_fn_mk]

/-- The "remarkable product" giving the differnece of two powers. -/
lemma sub_mul_sum_pow (a b : R) (n : ℕ) :
  (a - b) * ∑ i in finset.range (n + 1), a ^ i * b ^ (n - i) = a ^ (n + 1) - b ^ (n + 1) :=
begin
  induction n with n ih,
  { simp },
  calc (a - b) * ∑ (i : ℕ) in finset.range (n + 2), a ^ i * b ^ (n + 1 - i)
      = a * ((a - b) * (∑ (x : ℕ) in finset.range (n + 1), a ^ x * b ^ (n - x))) +
        (a - b) * (b * b ^ n) :
    by simp [finset.sum_range_succ', pow_succ, mul_assoc, ← finset.mul_sum, mul_add, mul_left_comm]
  ... = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * (b * b ^ n) : by rw ih
  ... = a ^ (n + 2) - b ^ (n + 2) : by ring_exp
end

lemma det_eq_of_eq_mul_det_one {n : Type*} [fintype n] [decidable_eq n] {A B : matrix n n R}
  (C : matrix n n R) (hC : det C = 1) (hA : A = B ⬝ C) : det A = det B :=
calc det A = det (B ⬝ C) : congr_arg _ hA
... = det B * det C : det_mul _ _
... = det B : by rw [hC, mul_one]

lemma det_eq_of_eq_det_one_mul {n : Type*} [fintype n] [decidable_eq n] {A B : matrix n n R}
  (C : matrix n n R) (hC : det C = 1) (hA : A = C ⬝ B) : det A = det B :=
calc det A = det (C ⬝ B) : congr_arg _ hA
... = det C * det B : det_mul _ _
... = det B : by rw [hC, one_mul]

@[simp] lemma update_row_eq_self {n : Type*} [fintype n] [decidable_eq n]
  (A : matrix n n R) {i : n} :
  A.update_row i (A i) = A :=
by { ext i', rw update_row_apply, split_ifs with h; simp [h] }

lemma det_update_row_add_self {n : Type*} [fintype n] [decidable_eq n]
  (A : matrix n n R) {i j : n} (hij : i ≠ j) :
  det (update_row A i (A i + A j)) = det A :=
by simp [det_update_row_add,
         det_zero_of_row_eq hij ((update_row_self).trans (update_row_ne hij.symm).symm)]

lemma det_update_row_add_smul_self {n : Type*} [fintype n] [decidable_eq n]
  (A : matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
  det (update_row A i (A i + c • A j)) = det A :=
by simp [det_update_row_add, det_update_row_smul,
  det_zero_of_row_eq hij ((update_row_self).trans (update_row_ne hij.symm).symm)]

lemma det_eq_of_forall_row_eq_smul_add_const_aux {n : Type*} [fintype n] [decidable_eq n]
  {A B : matrix n n R} {s : finset n} : ∀ (c : n → R) (hs : ∀ i, i ∉ s → c i = 0)
  (k : n) (hk : k ∉ s) (A_eq : ∀ i j, A i j = B i j + c i * B k j),
  det A = det B :=
begin
  revert B,
  refine s.induction_on _ _,
  { intros A c hs k hk A_eq,
    have : ∀ i, c i = 0,
    { intros i,
      specialize hs i,
      contrapose! hs,
      simp [hs] },
    congr,
    ext i j,
    rw [A_eq, this, zero_mul, add_zero], },
  { intros i s hi ih B c hs k hk A_eq,
    have hAi : A i = B i + c i • B k := funext (A_eq i),
    rw [@ih (update_row B i (A i)) (function.update c i 0), hAi,
        det_update_row_add_smul_self],
    { exact mt (λ h, show k ∈ insert i s, from h ▸ finset.mem_insert_self _ _) hk },
    { intros i' hi',
      rw function.update_apply,
      split_ifs with hi'i, { refl },
      { exact hs i' (λ h, hi' ((finset.mem_insert.mp h).resolve_left hi'i)) } },
    { exact λ h, hk (finset.mem_insert_of_mem h) },
    { intros i' j',
      rw [update_row_apply, function.update_apply],
      split_ifs with hi'i,
      { simp [hi'i] },
      rw [A_eq, update_row_ne (λ (h : k = i), hk $ h ▸ finset.mem_insert_self k s)] } }
end

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
lemma det_eq_of_forall_row_eq_smul_add_const {n : Type*} [fintype n] [decidable_eq n]
  {A B : matrix n n R} (c : n → R) (k : n) (hk : c k = 0)
  (A_eq : ∀ i j, A i j = B i j + c i * B k j) :
  det A = det B :=
det_eq_of_forall_row_eq_smul_add_const_aux c
  (λ i, not_imp_comm.mp $ λ hi, finset.mem_erase.mpr
    ⟨mt (λ (h : i = k), show c i = 0, from h.symm ▸ hk) hi, finset.mem_univ i⟩)
  k (finset.not_mem_erase k finset.univ) A_eq

@[simp] lemma cast_succ_lt_iff {n : ℕ} {i : fin n} {j : fin (n + 1)} :
  i.cast_succ < j ↔ i.succ ≤ j :=
fin.cases
  (⟨λ h, absurd h (nat.not_lt_zero _), λ h, absurd h i.succ_pos.not_le⟩)
  (λ j, by rw [fin.lt_iff_coe_lt_coe, fin.succ_le_succ_iff, fin.le_iff_coe_le_coe,
               fin.coe_cast_succ, fin.coe_succ, nat.lt_succ_iff])
  j

lemma det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : fin (n + 1)) :
  ∀ (c : fin n → R) (hc : ∀ (i : fin n), k < i.succ → c i = 0)
    {M N : matrix (fin n.succ) (fin n.succ) R}
    (h0 : ∀ j, M 0 j = N 0 j)
    (hsucc : ∀ (i : fin n) j, M i.succ j = N i.succ j + c i * M i.cast_succ j),
    det M = det N :=
begin
  refine fin.induction _ (λ k ih, _) k;
    intros c hc M N h0 hsucc,
  { congr,
    ext i j,
    refine fin.cases (h0 j) (λ i, _) i,
    rw [hsucc, hc i (fin.succ_pos _), zero_mul, add_zero] },

  set M' := update_row M k.succ (N k.succ) with hM',
  have hM : M = update_row M' k.succ (M' k.succ + c k • M k.cast_succ),
  { ext i j,
    by_cases hi : i = k.succ,
    { simp [hi, hM', hsucc, update_row_self] },
    rw [update_row_ne hi, hM', update_row_ne hi] },

  have k_ne_succ : k.cast_succ ≠ k.succ := (fin.cast_succ_lt_succ k).ne,
  have M_k : M k.cast_succ = M' k.cast_succ := (update_row_ne k_ne_succ).symm,

  rw [hM, M_k, det_update_row_add_smul_self M' k_ne_succ.symm, ih (function.update c k 0)],
  { intros i hi,
    rw [cast_succ_lt_iff, fin.succ_le_succ_iff] at hi,
    rw function.update_apply,
    split_ifs with hik, { refl },
    exact hc _ (fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (ne.symm hik))) },
  { rwa [hM', update_row_ne (fin.succ_ne_zero _).symm] },
  { intros i j,
    rw function.update_apply,
    split_ifs with hik,
    { rw [zero_mul, add_zero, hM', hik, update_row_self] },
    { rw [hM', update_row_ne ((fin.succ_injective _).ne hik), hsucc],
      by_cases hik2 : k < i,
      { simp [hc i (fin.succ_lt_succ_iff.mpr hik2)] },
      { rw update_row_ne,
        apply ne_of_lt,
        rwa [cast_succ_lt_iff, fin.succ_le_succ_iff, ← not_lt] } } },
end

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
lemma det_eq_of_forall_row_eq_smul_add_pred {n : ℕ}
  {A B : matrix (fin (n + 1)) (fin (n + 1)) R} (c : fin n → R)
  (A_zero : ∀ j, A 0 j = B 0 j)
  (A_succ : ∀ (i : fin n) j, A i.succ j = B i.succ j + c i * A i.cast_succ j) :
  det A = det B :=
det_eq_of_forall_row_eq_smul_add_pred_aux (fin.last _) c
  (λ i hi, absurd hi (not_lt_of_ge (fin.le_last _)))
  A_zero A_succ

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
lemma det_eq_of_forall_col_eq_smul_add_pred {n : ℕ}
  {A B : matrix (fin (n + 1)) (fin (n + 1)) R} (c : fin n → R)
  (A_zero : ∀ i, A i 0 = B i 0)
  (A_succ : ∀ i (j : fin n), A i j.succ = B i j.succ + c j * A i j.cast_succ) :
  det A = det B :=
by { rw [← det_transpose A, ← det_transpose B],
     exact det_eq_of_forall_row_eq_smul_add_pred c A_zero (λ i j, A_succ j i) }

lemma det_vandermonde {n : ℕ} (v : fin n → R) :
  det (vandermonde v) = ∏ i : fin n, ∏ j in finset.univ.filter (λ j, i < j), (v j - v i) :=
begin
  unfold vandermonde,

  induction n with n ih,
  { exact det_eq_one_of_card_eq_zero (fintype.card_fin 0) },

  calc det (λ (i j : fin n.succ), v i ^ (j : ℕ))
      = det (λ (i j : fin n.succ), @fin.cons _ (λ _, R)
               (v 0 ^ (j : ℕ))
               (λ i, v (fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :
    det_eq_of_forall_row_eq_smul_add_const (fin.cons 0 1) 0 (fin.cons_zero _ _) _
  ... = det (λ (i j : fin n), @fin.cons _ (λ _, R)
              (v 0 ^ (j.succ : ℕ))
              (λ (i : fin n), v (fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (fin.succ_above 0 i)) :
    by simp_rw [det_succ_row, fin.sum_univ_succ, fin.cons_zero, fin.cons_succ, fin.coe_zero,
                pow_zero, one_mul, sub_self, mul_zero, zero_mul, finset.sum_const_zero, add_zero]
  ... = det (λ (i j : fin n), (v (fin.succ i) - v 0) *
              (∑ k in finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ))) :
    by { congr, ext i j, rw [fin.succ_above_zero, fin.cons_succ, fin.coe_succ, sub_mul_sum_pow] }
  ... = (∏ (i : fin n), (v (fin.succ i) - v 0)) * det (λ (i j : fin n),
    (∑ k in finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ))) :
    det_mul_column (λ i, v (fin.succ i) - v 0) _
  ... = (∏ (i : fin n), (v (fin.succ i) - v 0)) * det (λ (i j : fin n), v (fin.succ i) ^ (j : ℕ)) :
    congr_arg ((*) _) _
  ... = ∏ i : fin n.succ, ∏ j in finset.univ.filter (λ j, i < j), (v j - v i) :
    by { simp_rw [ih (v ∘ fin.succ), fin.prod_univ_succ, prod_filter_zero_lt, prod_filter_succ_lt] },
  { intros i j,
    rw fin.cons_zero,
    refine fin.cases _ (λ i, _) i,
    { simp },
    rw [fin.cons_succ, fin.cons_succ, pi.one_apply],
    ring },
  { cases n,
    { simp only [det_eq_one_of_card_eq_zero (fintype.card_fin 0)] },
    apply det_eq_of_forall_col_eq_smul_add_pred (λ i, v 0),
    { intro j,
      simp },
    { intros i j,
      simp only [smul_eq_mul, pi.add_apply, fin.coe_succ, fin.coe_cast_succ, pi.smul_apply],
      rw [finset.sum_range_succ, nat.sub_self, pow_zero, mul_one, finset.mul_sum],
      congr' 1,
      refine finset.sum_congr rfl (λ i' hi', _),
      rw [mul_left_comm (v 0), nat.succ_sub, pow_succ],
      exact nat.lt_succ_iff.mp (finset.mem_range.mp hi') } }
end

end matrix
