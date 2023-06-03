/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse
import tactic.fin_cases

/-!
# Block matrices and their determinant

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a predicate `matrix.block_triangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → α`

## Main results
  * `matrix.det_of_block_triangular`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `matrix.det_of_upper_triangular` and `matrix.det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

open finset function order_dual
open_locale big_operators matrix

universes v

variables {α β m n o : Type*} {m' n' : α → Type*}
variables {R : Type v} [comm_ring R] {M N : matrix m m R} {b : m → α}

namespace matrix

section has_lt
variables [has_lt α]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then
`block_triangular M n b` says the matrix is block triangular. -/
def block_triangular (M : matrix m m R) (b : m → α) : Prop := ∀ ⦃i j⦄, b j < b i → M i j = 0

@[simp] protected lemma block_triangular.submatrix {f : n → m} (h : M.block_triangular b) :
  (M.submatrix f f).block_triangular (b ∘ f) :=
λ i j hij, h hij

lemma block_triangular_reindex_iff {b : n → α} {e : m ≃ n} :
  (reindex e e M).block_triangular b ↔ M.block_triangular (b ∘ e) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { convert h.submatrix,
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, equiv.symm_comp_self] },
  { convert h.submatrix,
    simp only [comp.assoc b e e.symm, equiv.self_comp_symm, comp.right_id] }
end

protected lemma block_triangular.transpose :
  M.block_triangular b → Mᵀ.block_triangular (to_dual ∘ b) := swap

@[simp] protected lemma block_triangular_transpose_iff {b : m → αᵒᵈ} :
  Mᵀ.block_triangular b ↔ M.block_triangular (of_dual ∘ b) := forall_swap

@[simp] lemma block_triangular_zero : block_triangular (0 : matrix m m R) b := λ i j h, rfl

protected lemma block_triangular.neg (hM : block_triangular M b) : block_triangular (-M) b :=
λ i j h, neg_eq_zero.2 $ hM h

lemma block_triangular.add (hM : block_triangular M b) (hN : block_triangular N b) :
  block_triangular (M + N) b :=
λ i j h, by simp_rw [pi.add_apply, hM h, hN h, zero_add]

lemma block_triangular.sub (hM : block_triangular M b) (hN : block_triangular N b) :
  block_triangular (M - N) b :=
λ i j h, by simp_rw [pi.sub_apply, hM h, hN h, sub_zero]

end has_lt

section preorder
variables [preorder α]

lemma block_triangular_diagonal [decidable_eq m] (d : m → R) :
  block_triangular (diagonal d) b :=
λ i j h, diagonal_apply_ne' d (λ h', ne_of_lt h (congr_arg _ h'))

lemma block_triangular_block_diagonal' [decidable_eq α] (d : Π (i : α), matrix (m' i) (m' i) R) :
  block_triangular (block_diagonal' d) sigma.fst :=
begin
  rintros ⟨i, i'⟩ ⟨j, j'⟩ h,
  apply block_diagonal'_apply_ne d i' j' (λ h', ne_of_lt h h'.symm),
end

lemma block_triangular_block_diagonal [decidable_eq α] (d : α → matrix m m R) :
  block_triangular (block_diagonal d) prod.snd :=
begin
  rintros ⟨i, i'⟩ ⟨j, j'⟩ h,
  rw [block_diagonal'_eq_block_diagonal, block_triangular_block_diagonal'],
  exact h
end

end preorder

section linear_order
variables [linear_order α]

lemma block_triangular.mul [fintype m]
  {M N : matrix m m R} (hM : block_triangular M b) (hN : block_triangular N b):
  block_triangular (M * N) b :=
begin
  intros i j hij,
  apply finset.sum_eq_zero,
  intros k hk,
  by_cases hki : b k < b i,
  { simp_rw [hM hki, zero_mul] },
  { simp_rw [hN (lt_of_lt_of_le hij (le_of_not_lt hki)), mul_zero] },
end

end linear_order

lemma upper_two_block_triangular [preorder α]
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) {a b : α} (hab : a < b) :
  block_triangular (from_blocks A B 0 D) (sum.elim (λ i, a) (λ j, b)) :=
by rintro (c | c) (d | d) hcd; simpa [hab.not_lt] using hcd <|> simp

/-! ### Determinant -/

variables [decidable_eq m] [fintype m] [decidable_eq n] [fintype n]

lemma equiv_block_det (M : matrix m m R) {p q : m → Prop} [decidable_pred p] [decidable_pred q]
  (e : ∀ x, q x ↔ p x) : (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
by convert matrix.det_reindex_self (equiv.subtype_equiv_right e) (to_square_block_prop M q)

@[simp] lemma det_to_square_block_id (M : matrix m m R) (i : m) :
  (M.to_square_block id i).det = M i i :=
begin
  letI : unique {a // id a = i} := ⟨⟨⟨i, rfl⟩⟩, λ j, subtype.ext j.property⟩,
  exact (det_unique _).trans rfl,
end

lemma det_to_block (M : matrix m m R) (p : m → Prop) [decidable_pred p] :
  M.det = (from_blocks (to_block M p p) (to_block M p $ λ j, ¬p j)
    (to_block M (λ j, ¬p j) p) $ to_block M (λ j, ¬p j) $ λ j, ¬p j).det :=
begin
  rw ←matrix.det_reindex_self (equiv.sum_compl p).symm M,
  rw [det_apply', det_apply'],
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
    matrix.submatrix_apply],
end

lemma two_block_triangular_det (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, ¬ p i → ∀ j, p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw det_to_block M p,
  convert det_from_blocks_zero₂₁ (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) (λ j, ¬p j)),
  ext,
  exact h ↑i i.2 ↑j j.2
end

lemma two_block_triangular_det' (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw [M.two_block_triangular_det (λ i, ¬ p i), mul_comm],
  simp_rw not_not,
  congr' 1,
  exact equiv_block_det _ (λ _, not_not.symm),
  simpa only [not_not] using h,
end

protected lemma block_triangular.det [decidable_eq α] [linear_order α] (hM : block_triangular M b) :
  M.det = ∏ a in univ.image b, (M.to_square_block b a).det :=
begin
  unfreezingI { induction hs : univ.image b using finset.strong_induction
    with s ih generalizing m },
  subst hs,
  casesI is_empty_or_nonempty m,
  { simp },
  let k := (univ.image b).max' (univ_nonempty.image _),
  rw two_block_triangular_det' M (λ i, b i = k),
  { have : univ.image b = insert k ((univ.image b).erase k),
    { rw insert_erase, apply max'_mem },
    rw [this, prod_insert (not_mem_erase _ _)],
    refine congr_arg _ _,
    let b' := λ i : {a // b a ≠ k}, b ↑i,
    have h' :  block_triangular (M.to_square_block_prop (λ i, b i ≠ k)) b' := hM.submatrix,
    have hb' : image b' univ = (image b univ).erase k,
    { convert image_subtype_ne_univ_eq_image_erase k b },
    rw ih _ (erase_ssubset $ max'_mem _ _) h' hb',
    refine finset.prod_congr rfl (λ l hl, _),
    let he : {a // b' a = l} ≃ {a // b a = l},
    { have hc : ∀ i, b i = l → b i ≠ k := λ i hi, ne_of_eq_of_ne hi (ne_of_mem_erase hl),
      exact equiv.subtype_subtype_equiv_subtype hc },
    simp only [to_square_block_def],
    rw ← matrix.det_reindex_self he.symm (λ (i j : {a // b a = l}), M ↑i ↑j),
    refl },
  { intros i hi j hj,
    apply hM,
    rw hi,
    apply lt_of_le_of_ne _ hj,
    exact finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _)) }
end

lemma block_triangular.det_fintype [decidable_eq α] [fintype α] [linear_order α]
  (h : block_triangular M b) :
  M.det = ∏ k : α, (M.to_square_block b k).det :=
begin
  refine h.det.trans (prod_subset (subset_univ _) $ λ a _ ha, _),
  have : is_empty {i // b i = a} := ⟨λ i, ha $ mem_image.2 ⟨i, mem_univ _, i.2⟩⟩,
  exactI det_is_empty,
end

lemma det_of_upper_triangular [linear_order m] (h : M.block_triangular id) :
  M.det = ∏ i : m, M i i :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  simp_rw [h.det, image_id, det_to_square_block_id],
end

lemma det_of_lower_triangular [linear_order m] (M : matrix m m R) (h : M.block_triangular to_dual) :
  M.det = ∏ i : m, M i i :=
by { rw ←det_transpose, exact det_of_upper_triangular h.transpose }

/-! ### Invertible -/

lemma block_triangular.to_block_inverse_mul_to_block_eq_one [linear_order α] [invertible M]
  (hM : block_triangular M b) (k : α) :
  M⁻¹.to_block (λ i, b i < k) (λ i, b i < k) ⬝ M.to_block (λ i, b i < k) (λ i, b i < k) = 1 :=
begin
  let p := (λ i, b i < k),
  have h_sum : M⁻¹.to_block p p ⬝ M.to_block p p +
      M⁻¹.to_block p (λ i, ¬ p i) ⬝ M.to_block (λ i, ¬ p i) p = 1,
    by rw [←to_block_mul_eq_add, inv_mul_of_invertible M, to_block_one_self],
  have h_zero : M.to_block (λ i, ¬ p i) p = 0,
  { ext i j,
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2)) },
  simpa [h_zero] using h_sum
end

/-- The inverse of an upper-left subblock of a block-triangular matrix `M` is the upper-left
subblock of `M⁻¹`. -/
lemma block_triangular.inv_to_block [linear_order α] [invertible M]
  (hM : block_triangular M b) (k : α) :
  (M.to_block (λ i, b i < k) (λ i, b i < k))⁻¹ = M⁻¹.to_block (λ i, b i < k) (λ i, b i < k) :=
inv_eq_left_inv $ hM.to_block_inverse_mul_to_block_eq_one k

/-- An upper-left subblock of an invertible block-triangular matrix is invertible. -/
def block_triangular.invertible_to_block [linear_order α] [invertible M]
 (hM : block_triangular M b) (k : α) :
  invertible (M.to_block (λ i, b i < k) (λ i, b i < k)) :=
invertible_of_left_inverse _ ((⅟M).to_block (λ i, b i < k) (λ i, b i < k)) $
  by simpa only [inv_of_eq_nonsing_inv] using hM.to_block_inverse_mul_to_block_eq_one k

/-- A lower-left subblock of the inverse of a block-triangular matrix is zero. This is a first step
towards `block_triangular.inv_to_block` below. -/
lemma to_block_inverse_eq_zero [linear_order α] [invertible M] (hM : block_triangular M b) (k : α) :
  M⁻¹.to_block (λ i, k ≤ b i) (λ i, b i < k) = 0 :=
begin
  let p := λ i, b i < k,
  let q := λ i, ¬ b i < k,
  have h_sum : M⁻¹.to_block q p ⬝ M.to_block p p + M⁻¹.to_block q q ⬝ M.to_block q p = 0,
  { rw [←to_block_mul_eq_add, inv_mul_of_invertible M, to_block_one_disjoint],
    rw disjoint_iff_inf_le,
    exact λ i h, h.1 h.2 },
  have h_zero : M.to_block q p = 0,
  { ext i j,
    simpa using hM (lt_of_lt_of_le j.2 $ le_of_not_lt i.2) },
  have h_mul_eq_zero : M⁻¹.to_block q p ⬝ M.to_block p p = 0 := by simpa [h_zero] using h_sum,
  haveI : invertible (M.to_block p p) := hM.invertible_to_block k,
  have : (λ i, k ≤ b i) = q := by { ext, exact not_lt.symm },
  rw [this, ← matrix.zero_mul (M.to_block p p)⁻¹, ← h_mul_eq_zero,
    mul_inv_cancel_right_of_invertible],
end

/-- The inverse of a block-triangular matrix is block-triangular. -/
lemma block_triangular_inv_of_block_triangular [linear_order α] [invertible M]
  (hM : block_triangular M b) :
  block_triangular M⁻¹ b :=
begin
  unfreezingI { induction hs : univ.image b using finset.strong_induction
    with s ih generalizing m },
  subst hs,
  intros i j hij,
  haveI : inhabited m := ⟨i⟩,
  let k := (univ.image b).max' (univ_nonempty.image _),
  let b' := λ i : {a // b a < k}, b ↑i,
  let A := M.to_block (λ i, b i < k) (λ j, b j < k),
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) $ mem_image_of_mem _ $ mem_univ _).eq_or_lt,
  { have : M⁻¹.to_block (λ i, k ≤ b i) (λ i, b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0,
    { simp only [to_block_inverse_eq_zero hM k, pi.zero_apply] },
    simp [this.symm] },
  haveI : invertible A := hM.invertible_to_block _,
  have hA : A.block_triangular b' := hM.submatrix,
  have hb' : image b' univ ⊂ image b univ,
  { convert image_subtype_univ_ssubset_image_univ k b _ (λ a, a < k) (lt_irrefl _),
    convert max'_mem _ _ },
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩, by simp_rw [b', subtype.coe_mk, hij],
  simp [hM.inv_to_block k, (ih (image b' univ) hb' hA rfl hij').symm],
end

end matrix
