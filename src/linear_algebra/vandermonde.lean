/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import order.conditionally_complete_lattice
import field_theory.adjoin
import field_theory.algebraic_closure
import field_theory.galois
import field_theory.primitive_element
import linear_algebra.bilinear_form
import linear_algebra.char_poly.coeff
import ring_theory.algebra_tower
import ring_theory.localization

/-!
# Vandermonde matrix

Defines the `vandermonde` matrix and gives its determinant.
-/

variables {R : Type*} [comm_ring R]

open_locale big_operators
open_locale matrix

namespace matrix

/-- A Vandermonde matrix has `1, v j, v j ^ 2, v j ^ 3, ...`. -/
def vandermonde {n : ℕ} (v : fin n → R) : matrix (fin n) (fin n) R :=
λ i j, v j ^ (i : ℕ)

/-- Multiplying each row with a scalar, scales the determinant with the product of all scales. -/
lemma det_row_mul {n : ℕ} (v : fin n → R) (M : matrix (fin n) (fin n) R) :
  det (λ i j, v j * M i j) = (∏ j, v j) * det M :=
begin
  induction n with n ih,
  { rw [det_eq_one_of_card_eq_zero, det_eq_one_of_card_eq_zero, fin.prod_univ_zero, mul_one];
    exact fintype.card_fin 0 },
  simp only [det_succ_row, ih (λ j, v j.succ), finset.mul_sum, fin.prod_univ_succ],
  apply finset.sum_congr rfl,
  intros x _,
  ring
end

lemma prod_filter_zero_lt {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in finset.univ.filter (λ (i : fin n.succ), 0 < i), v i = ∏ (j : fin n), v j.succ :=
finset.prod_bij
  (λ i hi, i.pred (ne_of_lt (finset.mem_filter.mp hi).2).symm)
  (λ i hi, finset.mem_univ _)
  (λ i hi, by rw fin.succ_pred)
  (λ i i' hi hi' h, fin.pred_inj.mp h)
  (λ j _, ⟨j.succ, finset.mem_filter.mpr ⟨finset.mem_univ _, fin.succ_pos _⟩, by rw fin.pred_succ⟩)

lemma fin.lt_pred {n : ℕ} {i : fin n} {j : fin n.succ} {hj : j ≠ 0} :
  i < j.pred hj ↔ i.succ < j :=
by { convert fin.succ_lt_succ_iff.symm, rw fin.succ_pred }

lemma prod_filter_succ_lt {n : ℕ} {v : fin n.succ → R} {i : fin n} :
  ∏ j in finset.univ.filter (λ (j : fin n.succ), i.succ < j), v j =
    ∏ j in finset.univ.filter (λ j, i < j), v j.succ :=
finset.prod_bij
  (λ j hj, j.pred (ne_of_lt (lt_trans (fin.zero_lt_succ i) (finset.mem_filter.mp hj).2)).symm)
  (λ j hj, finset.mem_filter.mpr ⟨finset.mem_univ _, fin.lt_pred.mpr (finset.mem_filter.mp hj).2⟩)
  (λ j hj, by rw fin.succ_pred)
  (λ j j' hj hj' h, fin.pred_inj.mp h)
  (λ j hj, ⟨j.succ, finset.mem_filter.mpr ⟨finset.mem_univ _,
    fin.succ_lt_succ_iff.mpr (finset.mem_filter.mp hj).2⟩, by rw fin.pred_succ⟩)

instance {n : Type*} [unique n] : unique (equiv.perm n) :=
{ default := 1,
  uniq := λ σ, equiv.ext (λ i, subsingleton.elim _ _) }

@[simp] lemma default_perm {n : Type*} : default (equiv.perm n) = 1 := rfl

/-- Although `unique` implies `decidable_eq` and `fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
lemma det_unique {n : Type*} [unique n] [d : decidable_eq n] [f : fintype n] (A : matrix n n R) :
  @det _ d f _ _ A = A (default n) (default n) :=
by simp [det, univ_unique]

lemma update_row_self' {R : Type*} {m n : Type*} [fintype m] [fintype n] [decidable_eq m]
  {M : matrix m n R} (i : m) : M.update_row i (M i) = M :=
by { ext, rw update_row_apply, split_ifs with h, { rw h }, refl }

lemma det_eq_of_row_eq_add_zero_aux {n : ℕ} {k : fin n.succ} :
  ∀ {M N : matrix (fin n.succ) (fin n.succ) R} {c : fin n → R}
    (h0 : M 0 = N 0)
    (hsucc : ∀ (i : fin n) (hi : i.succ ≤ k), M i.succ = N i.succ + c i • M 0)
    (hlast : ∀ (i : fin n.succ) (hi : k < i), M i = N i),
    det M = det N :=
begin
  refine fin.induction _ (λ k ih, _) k;
    intros M N c h0 hsucc hlast,
  { congr,
    ext i j,
    by_cases hi : i = 0,
    { rw [hi, h0] },
    rw hlast _ (nat.pos_iff_ne_zero.mpr
      (mt (λ (h : (i : ℕ) = (0 : fin n.succ)), fin.coe_injective h) hi)) },

  set M' := update_row M k.succ (N k.succ) with hM',
  have hM : M = update_row M' k.succ (M' k.succ + c k • M 0),
  { ext i j,
    by_cases hi : i = k.succ,
    { rw [hi, update_row_self, hM', update_row_self, hsucc _ (le_refl k.succ)] },
    rw [update_row_ne hi, hM', update_row_ne hi] },

  have zero_ne_succ : 0 ≠ k.succ := (fin.succ_ne_zero k).symm,

  rw [hM, det_update_row_add, update_row_self', det_update_row_smul,
    @det_zero_of_row_eq _ _ _ _ _ (M'.update_row _ _) _ _ zero_ne_succ,
    mul_zero, add_zero, ih],
  { rw [hM', update_row_ne (fin.succ_ne_zero _).symm, h0] },
  { intros i hi,
    have : i.succ < k.succ := lt_of_le_of_lt hi fin.lt_succ,
    rw [hM', update_row_ne (ne_of_lt this),
        update_row_ne zero_ne_succ, hsucc _ (le_of_lt this)] },
  { intros i hi,
    by_cases hik : i = k.succ,
    { rw [hik, hM', update_row_self] },
    { rw [hM', update_row_ne hik, hlast],
    exact lt_of_le_of_ne (fin.succ_le_iff.mpr hi) (ne.symm hik) } },
  { rw [update_row_ne zero_ne_succ, update_row_self, hM', update_row_ne zero_ne_succ] },
end

/-- If `M i j = N i j + c i * M 0 j`, then the determinant of `M` and `N` are the same. -/
lemma det_eq_of_row_eq_add_zero {n : ℕ}
  (M N : matrix (fin n.succ) (fin n.succ) R) (c : fin n → R)
  (h0 : M 0 = N 0) (hsucc : ∀ (i : fin n), M i.succ = N i.succ + c i • M 0) :
  det M = det N :=
det_eq_of_row_eq_add_zero_aux h0 (λ i _, hsucc i)
  (λ i (hi : fin.last n < i), false.elim (not_lt_of_ge (fin.le_last i) hi))

/-- If `M i j = N i j + c i * M i 0`, then the determinant of `M` and `N` are the same. -/
lemma det_eq_of_column_eq_add_zero {n : ℕ}
  (M N : matrix (fin n.succ) (fin n.succ) R) (c : fin n → R)
  (h0 : ∀ i, M i 0 = N i 0)
  (hsucc : ∀ (i : fin n.succ) (j : fin n), M i j.succ = N i j.succ + c j * M i 0) :
  det M = det N :=
begin
  rw [← det_transpose M, ← det_transpose N, det_eq_of_row_eq_add_zero],
  { ext i, exact h0 i },
  { intro j,
    ext i,
    rw [transpose_apply, hsucc i j, pi.add_apply, pi.smul_apply, smul_eq_mul],
    refl }
end

lemma det_eq_of_row_eq_add_pred_aux {n : ℕ} {k : fin n.succ} :
  ∀ {M N : matrix (fin n.succ) (fin n.succ) R} {c : fin n → R}
    (h0 : M 0 = N 0)
    (hsucc : ∀ (i : fin n) (hi : i.succ ≤ k), M i.succ = N i.succ + c i • M i.cast_succ)
    (hlast : ∀ (i : fin n.succ) (hi : k < i), M i = N i),
    det M = det N :=
begin
  refine fin.induction _ (λ k ih, _) k;
    intros M N c h0 hsucc hlast,
  { congr,
    ext i j,
    by_cases hi : i = 0,
    { rw [hi, h0] },
    rw hlast _ (nat.pos_iff_ne_zero.mpr
      (mt (λ (h : (i : ℕ) = (0 : fin n.succ)), fin.coe_injective h) hi)) },

  set M' := update_row M k.succ (N k.succ) with hM',
  have hM : M = update_row M' k.succ (M' k.succ + c k • M k.cast_succ),
  { ext i j,
    by_cases hi : i = k.succ,
    { rw [hi, update_row_self, hM', update_row_self, hsucc _ (le_refl k.succ)] },
    rw [update_row_ne hi, hM', update_row_ne hi] },

  have k_ne_succ : k.cast_succ ≠ k.succ := ne_of_lt fin.lt_succ,

  rw [hM, det_update_row_add, update_row_self', det_update_row_smul,
    @det_zero_of_row_eq _ _ _ _ _ (M'.update_row _ _) _ _ k_ne_succ,
    mul_zero, add_zero, ih],
  { rw [hM', update_row_ne (fin.succ_ne_zero _).symm, h0] },
  { intros i hi,
    have : i.succ < k.succ := lt_of_le_of_lt hi fin.lt_succ,
    rw [hM', update_row_ne (ne_of_lt this),
        update_row_ne (ne_of_lt (lt_trans (@fin.lt_succ _ i) this)), hsucc _ (le_of_lt this)] },
  { intros i hi,
    by_cases hik : i = k.succ,
    { rw [hik, hM', update_row_self] },
    { rw [hM', update_row_ne hik, hlast],
    exact lt_of_le_of_ne (fin.succ_le_iff.mpr hi) (ne.symm hik) } },
  { rw [update_row_ne k_ne_succ, update_row_self, hM', update_row_ne k_ne_succ] },
end

/-- If `M i j = N i j + c i * M (i - 1) j`, then the determinant of `M` and `N` are the same. -/
lemma det_eq_of_row_eq_add_pred {n : ℕ} (M N : matrix (fin n.succ) (fin n.succ) R) (c : fin n → R)
  (h0 : M 0 = N 0) (hsucc : ∀ (i : fin n), M i.succ = N i.succ + c i • M i.cast_succ) :
  det M = det N :=
det_eq_of_row_eq_add_pred_aux h0 (λ i _, hsucc i)
  (λ i (hi : fin.last n < i), false.elim (not_lt_of_ge (fin.le_last i) hi))

/-- If `M i j = N i j + c i * M i (j - 1)`, then the determinant of `M` and `N` are the same. -/
lemma det_eq_of_column_eq_add_pred {n : ℕ}
  (M N : matrix (fin n.succ) (fin n.succ) R) (c : fin n → R)
  (h0 : ∀ i, M i 0 = N i 0)
  (hsucc : ∀ (i : fin n.succ) (j : fin n), M i j.succ = N i j.succ + c j * M i j.cast_succ) :
  det M = det N :=
begin
  rw [← det_transpose M, ← det_transpose N, det_eq_of_row_eq_add_pred],
  { ext i, exact h0 i },
  { intro j,
    ext i,
    rw [transpose_apply, hsucc i j, pi.add_apply, pi.smul_apply, smul_eq_mul],
    refl }
end

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

lemma det_vandermonde {n : ℕ} (v : fin n → R) :
  det (vandermonde v) = ∏ i : fin n, ∏ j in finset.univ.filter (λ j, i < j), (v j - v i) :=
begin
  unfold vandermonde,
  induction n with n ih,
  { exact det_eq_one_of_card_eq_zero (fintype.card_fin 0) },

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
