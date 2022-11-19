/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.pi_L2

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

## Main definition

 * `matrix.is_hermitian` : a matrix `A : matrix n n α` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/

namespace matrix

variables {α β : Type*} {m n : Type*} {A : matrix n n α}

open_locale matrix

local notation `⟪`x`, `y`⟫` := @inner α (pi_Lp 2 (λ (_ : n), α)) _ x y

section non_unital_semiring

variables [non_unital_semiring α] [star_ring α] [non_unital_semiring β] [star_ring β]

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def is_hermitian (A : matrix n n α) : Prop := Aᴴ = A

lemma is_hermitian.eq {A : matrix n n α} (h : A.is_hermitian) : Aᴴ = A := h

@[ext]
lemma is_hermitian.ext {A : matrix n n α} : (∀ i j, star (A j i) = A i j) → A.is_hermitian :=
by { intros h, ext i j, exact h i j }

lemma is_hermitian.apply {A : matrix n n α} (h : A.is_hermitian) (i j : n) : star (A j i) = A i j :=
by { unfold is_hermitian at h, rw [← h, conj_transpose_apply, star_star, h] }

lemma is_hermitian.ext_iff {A : matrix n n α} : A.is_hermitian ↔ ∀ i j, star (A j i) = A i j :=
⟨is_hermitian.apply, is_hermitian.ext⟩

lemma is_hermitian_mul_conj_transpose_self [fintype n] (A : matrix n n α) :
  (A ⬝ Aᴴ).is_hermitian :=
by rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]

lemma is_hermitian_transpose_mul_self [fintype n] (A : matrix n n α) :
  (Aᴴ ⬝ A).is_hermitian :=
by rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]

lemma is_hermitian_conj_transpose_mul_mul [fintype m] {A : matrix m m α} (B : matrix m n α)
  (hA : A.is_hermitian) : (Bᴴ ⬝ A ⬝ B).is_hermitian :=
by simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
  matrix.mul_assoc]

lemma is_hermitian_mul_mul_conj_transpose [fintype m] {A : matrix m m α} (B : matrix n m α)
  (hA : A.is_hermitian) : (B ⬝ A ⬝ Bᴴ).is_hermitian :=
by simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
  matrix.mul_assoc]

lemma is_hermitian_add_transpose_self (A : matrix n n α) :
  (A + Aᴴ).is_hermitian :=
by simp [is_hermitian, add_comm]

lemma is_hermitian_transpose_add_self (A : matrix n n α) :
  (Aᴴ + A).is_hermitian :=
by simp [is_hermitian, add_comm]

@[simp] lemma is_hermitian_zero :
  (0 : matrix n n α).is_hermitian :=
conj_transpose_zero

@[simp] lemma is_hermitian.map {A : matrix n n α} (h : A.is_hermitian) (f : α → β)
  (hf : function.semiconj f star star) :
  (A.map f).is_hermitian :=
(conj_transpose_map f hf).symm.trans $ h.eq.symm ▸ rfl

lemma is_hermitian.transpose {A : matrix n n α} (h : A.is_hermitian) :
  Aᵀ.is_hermitian :=
by { rw [is_hermitian, conj_transpose, transpose_map], congr, exact h }

@[simp] lemma is_hermitian_transpose_iff (A : matrix n n α) :
  Aᵀ.is_hermitian ↔ A.is_hermitian :=
⟨by { intro h, rw [← transpose_transpose A], exact is_hermitian.transpose h },
  is_hermitian.transpose⟩

lemma is_hermitian.conj_transpose {A : matrix n n α} (h : A.is_hermitian) :
  Aᴴ.is_hermitian :=
h.transpose.map _ $ λ _, rfl

@[simp] lemma is_hermitian_conj_transpose_iff (A : matrix n n α) :
  Aᴴ.is_hermitian ↔ A.is_hermitian :=
⟨by { intro h, rw [← conj_transpose_conj_transpose A], exact is_hermitian.conj_transpose h },
  is_hermitian.conj_transpose⟩

@[simp] lemma is_hermitian.add {A B : matrix n n α} (hA : A.is_hermitian) (hB : B.is_hermitian) :
  (A + B).is_hermitian :=
(conj_transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp] lemma is_hermitian.submatrix {A : matrix n n α} (h : A.is_hermitian) (f : m → n) :
  (A.submatrix f f).is_hermitian :=
(conj_transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp] lemma is_hermitian_submatrix_equiv {A : matrix n n α} (e : m ≃ n) :
  (A.submatrix e e).is_hermitian ↔ A.is_hermitian :=
⟨λ h, by simpa using h.submatrix e.symm, λ h, h.submatrix _⟩

/-- The real diagonal matrix `diagonal v` is hermitian. -/
@[simp] lemma is_hermitian_diagonal [decidable_eq n] (v : n → ℝ) :
  (diagonal v).is_hermitian :=
diagonal_conj_transpose _

/-- A block matrix `A.from_blocks B C D` is hermitian,
    if `A` and `D` are hermitian and `Bᴴ = C`. -/
lemma is_hermitian.from_blocks
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
  (hA : A.is_hermitian) (hBC : Bᴴ = C) (hD : D.is_hermitian) :
  (A.from_blocks B C D).is_hermitian :=
begin
  have hCB : Cᴴ = B, {rw ← hBC, simp},
  unfold matrix.is_hermitian,
  rw from_blocks_conj_transpose,
  congr;
  assumption
end

/-- This is the `iff` version of `matrix.is_hermitian.from_blocks`. -/
lemma is_hermitian_from_blocks_iff
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α} :
  (A.from_blocks B C D).is_hermitian ↔ A.is_hermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.is_hermitian :=
⟨λ h, ⟨congr_arg to_blocks₁₁ h, congr_arg to_blocks₂₁ h,
       congr_arg to_blocks₁₂ h, congr_arg to_blocks₂₂ h⟩,
 λ ⟨hA, hBC, hCB, hD⟩, is_hermitian.from_blocks hA hBC hD⟩

end non_unital_semiring

section semiring

variables [semiring α] [star_ring α] [semiring β] [star_ring β]

@[simp] lemma is_hermitian_one [decidable_eq n] :
  (1 : matrix n n α).is_hermitian :=
conj_transpose_one

end semiring

section ring

variables [ring α] [star_ring α] [ring β] [star_ring β]

@[simp] lemma is_hermitian.neg {A : matrix n n α} (h : A.is_hermitian) :
  (-A).is_hermitian :=
(conj_transpose_neg _).trans (congr_arg _ h)

@[simp] lemma is_hermitian.sub {A B : matrix n n α} (hA : A.is_hermitian) (hB : B.is_hermitian) :
  (A - B).is_hermitian :=
(conj_transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

end ring

section comm_ring

variables [comm_ring α] [star_ring α]

lemma is_hermitian.inv [fintype m] [decidable_eq m] {A : matrix m m α}
  (hA : A.is_hermitian) : A⁻¹.is_hermitian :=
by simp [is_hermitian, conj_transpose_nonsing_inv, hA.eq]

@[simp] lemma is_hermitian_inv [fintype m] [decidable_eq m] (A : matrix m m α) [invertible A]:
  (A⁻¹).is_hermitian ↔ A.is_hermitian :=
⟨λ h, by {rw [← inv_inv_of_invertible A], exact is_hermitian.inv h }, is_hermitian.inv⟩

lemma is_hermitian.adjugate [fintype m] [decidable_eq m] {A : matrix m m α}
  (hA : A.is_hermitian) : A.adjugate.is_hermitian :=
by simp [is_hermitian, adjugate_conj_transpose, hA.eq]

end comm_ring

section is_R_or_C
open is_R_or_C

variables [is_R_or_C α] [is_R_or_C β]

/-- The diagonal elements of a complex hermitian matrix are real. -/
lemma is_hermitian.coe_re_apply_self {A : matrix n n α} (h : A.is_hermitian) (i : n) :
  (re (A i i) : α) = A i i :=
by rw [←eq_conj_iff_re, ←star_def, ←conj_transpose_apply, h.eq]

/-- The diagonal elements of a complex hermitian matrix are real. -/
lemma is_hermitian.coe_re_diag {A : matrix n n α} (h : A.is_hermitian) :
  (λ i, (re (A.diag i) : α)) = A.diag :=
funext h.coe_re_apply_self

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
lemma is_hermitian_iff_is_symmetric [fintype n] [decidable_eq n] {A : matrix n n α} :
  is_hermitian A ↔ linear_map.is_symmetric
    ((pi_Lp.linear_equiv 2 α (λ _ : n, α)).symm.conj A.to_lin' : module.End α (pi_Lp 2 _)) :=
begin
  rw [linear_map.is_symmetric, (pi_Lp.equiv 2 (λ _ : n, α)).symm.surjective.forall₂],
  simp only [linear_equiv.conj_apply, linear_map.comp_apply, linear_equiv.coe_coe,
    pi_Lp.linear_equiv_apply, pi_Lp.linear_equiv_symm_apply, linear_equiv.symm_symm],
  simp_rw [euclidean_space.inner_eq_star_dot_product, equiv.apply_symm_apply, to_lin'_apply,
    star_mul_vec, dot_product_mul_vec],
  split,
  { rintro (h : Aᴴ = A) x y,
    rw h },
  { intro h,
    ext i j,
    simpa only [(pi.single_star i 1).symm, ← star_mul_vec, mul_one, dot_product_single,
      single_vec_mul, star_one, one_mul] using
        h (@pi.single _ _ _ (λ i, add_zero_class.to_has_zero α) i 1)
          (@pi.single _ _ _ (λ i, add_zero_class.to_has_zero α) j 1) }
end

end is_R_or_C

end matrix
