/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Jeremy Avigad, Johan Commelin
-/
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def

/-! # Schur complement

This file proves properties of the Schur complement `D - C A⁻¹ B` of a block matrix `[A B; C D]`.

The determinant of a block matrix in terms of the Schur complement is expressed in the lemmas
`matrix.det_from_blocks₁₁` and `matrix.det_from_blocks₂₂` in the file
`linear_algebra.matrix.nonsingular_inverse`.

## Main result

 * `matrix.schur_complement_pos_semidef_iff` : If a matrix `A` is positive definite, then `[A B; Bᴴ
  D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/

namespace matrix

open_locale matrix
variables {n : Type*} {m : Type*} {R : Type*} [comm_ring R] [star_ring R]

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix

lemma schur_complement_eq₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m R} (B : matrix m n R) (D : matrix n n R) (x : m → R) (y : n → R)
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
  (A : matrix m m R) (B : matrix m n R) {D : matrix n n R} (x : m → R) (y : n → R)
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

end matrix

namespace matrix

open_locale matrix
variables {n : Type*} {m : Type*}
  {R : Type*} [ordered_comm_ring R] [star_ring R]

lemma is_hermitian.from_blocks₁₁ [fintype m] [decidable_eq m]
  {A : matrix m m R} (B : matrix m n R) (D : matrix n n R)
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
  (A : matrix m m R) (B : matrix m n R) {D : matrix n n R}
  (hD : D.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).is_hermitian :=
begin
  rw [←is_hermitian_minor_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_minor_sum_swap_sum_swap],
  convert is_hermitian.from_blocks₁₁ _ _ hD; simp
end

lemma pos_semidef.from_blocks₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m R} (B : matrix m n R) (D : matrix n n R)
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
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hA.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

lemma pos_semidef.from_blocks₂₂ [fintype m] [fintype n] [decidable_eq n]
  (A : matrix m m R) (B : matrix m n R) {D : matrix n n R}
  (hD : D.pos_def) [invertible D] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).pos_semidef :=
begin
  rw [pos_semidef, is_hermitian.from_blocks₂₂ _ _ hD.1],
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    have := h.2 (x ⊕ᵥ - ((D⁻¹ ⬝ Bᴴ).mul_vec x)),
    rw [dot_product_mul_vec, schur_complement_eq₂₂ A B _ _ hD.1, add_neg_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq₂₂ A B _ _ hD.1],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hD.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

end matrix
