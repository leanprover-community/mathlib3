/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin
-/
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C⬝A⁻¹⬝B`.

## Main results

 * `matrix.det_from_blocks₁₁`, `matrix.det_from_blocks₂₂`: determinant of a block matrix in terms of
   the Schur complement.
 * `matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.
 * `matrix.schur_complement_pos_semidef_iff` : If a matrix `A` is positive definite, then
  `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/

variables {l m n α : Type*}

namespace matrix
open_locale matrix

section comm_ring
variables [fintype l] [fintype m] [fintype n]
variables [decidable_eq l] [decidable_eq m] [decidable_eq n]
variables [comm_ring α]

/-- LDU decomposition of a block matrix with an invertible top-left corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₁₁
  (A : matrix m m α) (B : matrix m n α) (C : matrix l m α) (D : matrix l n α) [invertible A] :
  from_blocks A B C D =
    from_blocks 1 0 (C⬝⅟A) 1 ⬝ from_blocks A 0 0 (D - C⬝(⅟A)⬝B) ⬝ from_blocks 1 (⅟A⬝B) 0 1 :=
by simp only [from_blocks_multiply, matrix.mul_zero, matrix.zero_mul, add_zero, zero_add,
      matrix.one_mul, matrix.mul_one, matrix.inv_of_mul_self, matrix.mul_inv_of_self_assoc,
        matrix.mul_inv_of_mul_self_cancel, matrix.mul_assoc, add_sub_cancel'_right]

/-- LDU decomposition of a block matrix with an invertible bottom-right corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₂₂
  (A : matrix l m α) (B : matrix l n α) (C : matrix n m α) (D : matrix n n α) [invertible D] :
  from_blocks A B C D =
    from_blocks 1 (B⬝⅟D) 0 1 ⬝ from_blocks (A - B⬝⅟D⬝C) 0 0 D ⬝ from_blocks 1 0 (⅟D ⬝ C) 1 :=
(matrix.reindex (equiv.sum_comm _ _) (equiv.sum_comm _ _)).injective $ by
  simpa [reindex_apply, equiv.sum_comm_symm,
    ←submatrix_mul_equiv _ _ _ (equiv.sum_comm n m),
    ←submatrix_mul_equiv _ _ _ (equiv.sum_comm n l),
    equiv.sum_comm_apply, from_blocks_submatrix_sum_swap_sum_swap]
    using from_blocks_eq_of_invertible₁₁ D C B A

/-! ### Invertibility of block matrices -/

section invertible
variables [fintype m] [decidable_eq m]

def matrix.ext_iff_block {A B : matrix (m ⊕ n) (m ⊕ n) α} :
  A = B ↔ A.to_blocks₁₁ = B.to_blocks₁₁ ∧ A.to_blocks₁₂ = B.to_blocks₁₂ ∧
          A.to_blocks₂₁ = B.to_blocks₂₁ ∧ A.to_blocks₂₂ = B.to_blocks₂₂ :=
⟨λ h, h ▸ ⟨rfl, rfl, rfl, rfl⟩, λ ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩,
  by rw [←from_blocks_to_blocks A, ←from_blocks_to_blocks B, h₁₁, h₁₂, h₂₁, h₂₂]⟩

@[simp] def from_blocks_inj
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
  {A' : matrix m m α} {B' : matrix m n α} {C' : matrix n m α} {D' : matrix n n α} :
  from_blocks A B C D = from_blocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
matrix.ext_iff_block

/- LU decomposition of a block matrix with an invertible top-left corner. -/
lemma from_blocks_eq_of_invertible₁₁
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α) [invertible A] :
  from_blocks A B C D =
    from_blocks 1 0 (C⬝⅟A) 1 ⬝ from_blocks A 0 0 (D - C⬝(⅟A)⬝B) ⬝ from_blocks 1 (⅟A⬝B) 0 1 :=
by simp only [from_blocks_multiply, matrix.mul_zero, matrix.zero_mul, add_zero, zero_add,
      matrix.one_mul, matrix.mul_one, matrix.inv_of_mul_self, matrix.mul_inv_of_self_assoc,
        matrix.mul_inv_of_mul_self_cancel, matrix.mul_assoc, add_sub_cancel'_right]

/- LU decomposition of a block matrix with an invertible bottom-right corner. -/
lemma from_blocks_eq_of_invertible₂₂
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α) [invertible D] :
  from_blocks A B C D =
    from_blocks 1 (B⬝⅟D) 0 1 ⬝ from_blocks (A - B⬝⅟D⬝C) 0 0 D ⬝ from_blocks 1 0 (⅟D ⬝ C) 1 :=
(matrix.reindex (equiv.sum_comm _ _) (equiv.sum_comm _ _)).injective $ by
  simpa [reindex_apply, sum_comm_symm, ←submatrix_mul_equiv _ _ _ (equiv.sum_comm n m),
    (show ⇑(equiv.sum_comm n m) = sum.swap, from rfl), from_blocks_submatrix_sum_swap_sum_swap]
    using from_blocks_eq_of_invertible₁₁ D C B A

lemma from_blocks₂₂_invertible_aux'
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] (A' : matrix m m α) :
  (from_blocks
    (A')         (-(A'⬝B⬝⅟D))
    (-(⅟D⬝C⬝A')) (⅟D + ⅟D⬝C⬝A'⬝B⬝⅟D)) ⬝ from_blocks A B C D =
      from_blocks (A' ⬝ (A - B⬝⅟D⬝C)) 0 (⅟ D ⬝ C ⬝ (1 - (A' ⬝ (A - B⬝⅟D⬝C)))) 1 :=
begin
  rw [from_blocks_multiply, from_blocks_inj],
  simp_rw [matrix.neg_mul, ←sub_eq_add_neg, matrix.mul_sub, matrix.add_mul,
    matrix.mul_inv_of_mul_self_cancel _, sub_self, matrix.inv_of_mul_self, ←matrix.mul_assoc,
    neg_add_eq_iff_eq_add, add_comm, eq_self_iff_true, true_and, and_true,
      matrix.mul_one, sub_sub_eq_add_sub, ←add_sub_assoc, add_sub_cancel'],
end

lemma from_blocks₂₂_invertible_aux
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] (A' : matrix m m α) :
  (from_blocks
    (A')         (-(A'⬝B⬝⅟D))
    (-(⅟D⬝C⬝A')) (⅟D + ⅟D⬝C⬝A'⬝B⬝⅟D)) ⬝ from_blocks A B C D = 1 ↔ A' ⬝ (A - B⬝⅟D⬝C) = 1 :=
begin
  rw [from_blocks_multiply, ←from_blocks_one, from_blocks_inj],
  simp_rw [matrix.neg_mul, ←sub_eq_add_neg, matrix.mul_sub, matrix.add_mul,
    matrix.mul_inv_of_mul_self_cancel _, sub_self, matrix.inv_of_mul_self, ←matrix.mul_assoc,
    neg_add_eq_iff_eq_add, add_zero, add_comm, eq_self_iff_true, true_and, and_true,
    sub_eq_iff_eq_add],
  refine and_iff_left_of_imp _,
  intro h,
  simp_rw [matrix.mul_assoc, h, matrix.mul_add, matrix.mul_one, ←matrix.mul_assoc],
end

lemma from_blocks₁₁_invertible_aux
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] (D' : matrix n n α) :
  (from_blocks
      (⅟A + ⅟A⬝B⬝D'⬝C⬝⅟A) (-(⅟A⬝B⬝D'))
      (-(D'⬝C⬝⅟A))        (D')) ⬝ from_blocks A B C D = 1 ↔ D' ⬝ (D - C⬝⅟A⬝B) = 1 :=
begin
  -- prove by reordering
  rw [←from_blocks₂₂_invertible_aux, ←from_blocks_submatrix_sum_swap_sum_swap,
    ←from_blocks_submatrix_sum_swap_sum_swap D,
    (show sum.swap = (equiv.sum_comm n m).symm, from rfl), submatrix_mul_equiv, ←reindex_apply,
      equiv.apply_eq_iff_eq_symm_apply, reindex_symm, reindex_apply, submatrix_one_equiv],
end

/-- A block matrix is invertible if the bottom right corner and the corresponding schur complement
is. -/
def from_blocks₂₂_invertible
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] [invertible (A - B⬝⅟D⬝C)] :
  invertible (from_blocks A B C D) :=
by let A' := A - B⬝⅟D⬝C; have i1 : invertible A' := ‹_›; exactI
invertible_of_left_inverse _
  (from_blocks
      (⅟A')         (-(⅟A'⬝B⬝⅟D))
      (-(⅟D⬝C⬝⅟A')) (⅟D + ⅟D⬝C⬝⅟A'⬝B⬝⅟D))
  (by rw [from_blocks₂₂_invertible_aux, matrix.inv_of_mul_self])

lemma inv_of_from_blocks₂₂_eq
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] [invertible (A - B⬝⅟D⬝C)] [invertible (from_blocks A B C D)] :
  ⅟(from_blocks A B C D) = from_blocks
      (⅟(A - B⬝⅟D⬝C))          (-(⅟(A - B⬝⅟D⬝C)⬝B⬝⅟D))
      (-(⅟D⬝C⬝⅟(A - B⬝⅟D⬝C))) (⅟D + ⅟D⬝C⬝⅟(A - B⬝⅟D⬝C)⬝B⬝⅟D):=
begin
  letI := from_blocks₂₂_invertible A B C D,
  haveI := invertible.subsingleton (from_blocks A B C D),
  convert (rfl : ⅟(from_blocks A B C D) = _),
end

/-- A block matrix is invertible if the top left corner and the corresponding schur complement
is. -/
def from_blocks₁₁_invertible
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] [invertible (D - C⬝⅟A⬝B)] :
  invertible (from_blocks A B C D) :=
by let D' := D - C⬝⅟A⬝B; have i1 : invertible D' := ‹_›; exactI
invertible_of_left_inverse _
  (from_blocks
      (⅟A + ⅟A⬝B⬝⅟D'⬝C⬝⅟A) (-(⅟A⬝B⬝⅟D'))
      (-(⅟D'⬝C⬝⅟A))        (⅟D'))
  (by rw [from_blocks₁₁_invertible_aux, matrix.inv_of_mul_self])

lemma inv_of_from_blocks₁₁_eq
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] [invertible (D - C⬝⅟A⬝B)] [invertible (from_blocks A B C D)] :
  ⅟(from_blocks A B C D) = from_blocks
      (⅟A + ⅟A⬝B⬝⅟(D - C⬝⅟A⬝B)⬝C⬝⅟A) (-(⅟A⬝B⬝⅟(D - C⬝⅟A⬝B)))
      (-(⅟(D - C⬝⅟A⬝B)⬝C⬝⅟A)) (⅟(D - C⬝⅟A⬝B)) :=
begin
  letI := from_blocks₁₁_invertible A B C D,
  haveI := invertible.subsingleton (from_blocks A B C D),
  convert (rfl : ⅟(from_blocks A B C D) = _),
end


def invertible_of_from_blocks₂₂_invertible
  (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] [invertible (from_blocks A B C D)] : invertible (A - B⬝⅟D⬝C) :=
let A' := (⅟(from_blocks A B C D)).to_blocks₁₁ in
invertible_of_left_inverse _ A' $ begin
  rw ←from_blocks₂₂_invertible_aux,
  refine eq.trans _ (from_blocks A B C D).inv_of_mul_self,
  congr,
end

end invertible

/-! ### Lemmas about `matrix.det` -/

section det

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
lemma det_from_blocks₁₁ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] : (matrix.from_blocks A B C D).det = det A * det (D - C ⬝ (⅟A) ⬝ B) :=
by rw [from_blocks_eq_of_invertible₁₁, det_mul, det_mul, det_from_blocks_zero₂₁,
  det_from_blocks_zero₂₁, det_from_blocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]

@[simp] lemma det_from_blocks_one₁₁ (B : matrix m n α) (C : matrix n m α) (D : matrix n n α) :
  (matrix.from_blocks 1 B C D).det = det (D - C ⬝ B) :=
begin
  haveI : invertible (1 : matrix m m α) := invertible_one,
  rw [det_from_blocks₁₁, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
lemma det_from_blocks₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] : (matrix.from_blocks A B C D).det = det D * det (A - B ⬝ (⅟D) ⬝ C) :=
begin
  have : from_blocks A B C D
    = (from_blocks D C B A).submatrix (equiv.sum_comm _ _) (equiv.sum_comm _ _),
  { ext i j,
    cases i; cases j; refl },
  rw [this, det_submatrix_equiv_self, det_from_blocks₁₁],
end

@[simp] lemma det_from_blocks_one₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) :
  (matrix.from_blocks A B C 1).det = det (A - B ⬝ C) :=
begin
  haveI : invertible (1 : matrix n n α) := invertible_one,
  rw [det_from_blocks₂₂, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
lemma det_one_add_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 + A ⬝ B) = det (1 + B ⬝ A) :=
calc  det (1 + A ⬝ B)
    = det (from_blocks 1 (-A) B 1) : by rw [det_from_blocks_one₂₂, matrix.neg_mul, sub_neg_eq_add]
... = det (1 + B ⬝ A)              : by rw [det_from_blocks_one₁₁, matrix.mul_neg, sub_neg_eq_add]

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
lemma det_mul_add_one_comm (A : matrix m n α) (B : matrix n m α) :
  det (A ⬝ B + 1) = det (B ⬝ A + 1) :=
by rw [add_comm, det_one_add_mul_comm, add_comm]

lemma det_one_sub_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 - A ⬝ B) = det (1 - B ⬝ A) :=
by rw [sub_eq_add_neg, ←matrix.neg_mul, det_one_add_mul_comm, matrix.mul_neg, ←sub_eq_add_neg]

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
lemma det_one_add_col_mul_row (u v : m → α) : det (1 + col u ⬝ row v) = 1 + v ⬝ᵥ u :=
by rw [det_one_add_mul_comm, det_unique, pi.add_apply, pi.add_apply, matrix.one_apply_eq,
       matrix.row_mul_col_apply]

end det

end comm_ring

/-! ### Lemmas about `ℝ` and `ℂ`-/

section is_R_or_C

open_locale matrix
variables {𝕜 : Type*} [is_R_or_C 𝕜]

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix

lemma schur_complement_eq₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜)
  [invertible A] (hA : A.is_hermitian) :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star (x + (A⁻¹ ⬝ B).mul_vec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mul_vec y) +
    vec_mul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
begin
  simp [function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hA.eq,
    conj_transpose_nonsing_inv, star_mul_vec],
  abel
end

lemma schur_complement_eq₂₂ [fintype m] [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜)
  [invertible D] (hD : D.is_hermitian) :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star ((D⁻¹ ⬝ Bᴴ).mul_vec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mul_vec x + y) +
    vec_mul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x :=
begin
  simp [function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hD.eq,
    conj_transpose_nonsing_inv, star_mul_vec],
  abel
end

lemma is_hermitian.from_blocks₁₁ [fintype m] [decidable_eq m]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜)
  (hA : A.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian :=
begin
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian,
  { apply is_hermitian_conj_transpose_mul_mul,
    apply hA.inv },
  rw [is_hermitian_from_blocks_iff],
  split,
  { intro h,
    apply is_hermitian.sub h.2.2.2 hBAB },
  { intro h,
    refine ⟨hA, rfl, conj_transpose_conj_transpose B, _⟩,
    rw ← sub_add_cancel D,
    apply is_hermitian.add h hBAB }
end

lemma is_hermitian.from_blocks₂₂ [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜}
  (hD : D.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).is_hermitian :=
begin
  rw [←is_hermitian_submatrix_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_submatrix_sum_swap_sum_swap],
  convert is_hermitian.from_blocks₁₁ _ _ hD; simp
end

lemma pos_semidef.from_blocks₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜)
  (hA : A.pos_def) [invertible A] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).pos_semidef :=
begin
  rw [pos_semidef, is_hermitian.from_blocks₁₁ _ _ hA.1],
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    have := h.2 (- ((A⁻¹ ⬝ B).mul_vec x) ⊕ᵥ x),
    rw [dot_product_mul_vec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1,
      map_add],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hA.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

lemma pos_semidef.from_blocks₂₂ [fintype m] [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜}
  (hD : D.pos_def) [invertible D] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).pos_semidef :=
begin
  rw [←pos_semidef_submatrix_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_submatrix_sum_swap_sum_swap],
  convert pos_semidef.from_blocks₁₁ _ _ hD; apply_instance <|> simp
end

end is_R_or_C

end matrix
