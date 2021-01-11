/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Shing Tak Lam
-/
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse
import data.complex.basic

/-!
# The Unitrary Group O(n)

This file defines elements of the unitary group `unitary_group n`, also written `U(n)`,
consisting of all `n` by `n` complex matrices where the conjugate transpose is the inverse.
In addition, we define the group structure on `unitary_group n` and the embedding into the
general linear group `general_linear_group ℂ (n → ℂ)`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `U(n) → GLₙ(ℝ)`

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group

-/

namespace matrix
universe u
open linear_map

section

variables {n m : Type*} [fintype n] [fintype m] [decidable_eq n] [decidable_eq m]

/--
  The conjugate transpose of a matrix, defined to be a the element-wise conjugate of the transpose.
-/
def conj_transpose (M : matrix n m ℂ) : matrix m n ℂ :=
  M.transpose.map complex.conj

localized "postfix `†`:1500 := conj_transpose" in matrix

lemma conj_transpose_eq_transpose_map_conj (M : matrix n m ℂ) : M† = (M.map complex.conj).transpose :=
begin
  ext; simp only [conj_transpose, map_apply, transpose_apply],
end

@[simp]
lemma conj_transpose_mul {p : Type*} [fintype p] [decidable_eq p] (M : matrix n m ℂ) (N : matrix m p ℂ) :
  (matrix.mul M N)† = matrix.mul N† M† := by simp [conj_transpose]

@[simp]
lemma conj_transpose_one : (1 : matrix n n ℂ)† = 1 := by simp [conj_transpose]

@[simp]
lemma conj_transpose_conj_transpose (M : matrix n m ℂ) : M†† = M :=
by simp [conj_transpose, matrix.transpose_map, function.involutive.comp_self complex.conj_involutive]

end

open_locale matrix

section

variables (n : Type u) [fintype n] [decidable_eq n]

/--
  `unitary_group n` is the group of `n` by `n` complex matrices where the conjugate transpose is
  the inverse.
-/
def unitary_group := {M : matrix n n ℂ // matrix.mul M† M = 1}

end

namespace unitary_group

variables {n : Type u} [decidable_eq n] [fintype n]

instance coe_matrix : has_coe (unitary_group n) (matrix n n ℂ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (unitary_group n) :=
{ F   := λ _, n → n → ℂ,
  coe := λ A, A.val }

/--
  `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

  After the group structure on `unitary_group n` is defined,
  we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : unitary_group n) := matrix.to_lin' A

lemma ext_iff (A B : unitary_group n) : A = B ↔ ∀ i j, A i j = B i j :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : unitary_group n) : (∀ i j, A i j = B i j) → A = B :=
(unitary_group.ext_iff A B).mpr

instance : has_inv (unitary_group n) :=
⟨λ A, ⟨A.1†, matrix.nonsing_inv_left_right _ _ $
  by { dsimp only, rw [conj_transpose_conj_transpose, A.2]}⟩⟩

noncomputable instance : has_mul (unitary_group n) :=
⟨λ A B, ⟨matrix.mul A.1  B.1, by rw [conj_transpose_mul, ←matrix.mul_assoc,
                                     matrix.mul_assoc _ _ A.1, A.2, matrix.mul_one, B.2],⟩⟩

instance : has_one (unitary_group n) :=
⟨⟨1, by rw [conj_transpose_one, matrix.one_mul]⟩⟩

instance : inhabited (unitary_group n) := ⟨1⟩

section coe_lemmas

variables (A B : unitary_group n)

@[simp] lemma inv_val : ↑(A⁻¹) = A† := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = A† := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : unitary_group n) = (1 : matrix n n ℂ) := rfl

@[simp] lemma one_apply : ⇑(1 : unitary_group n) = (1 : matrix n n ℂ) := rfl

@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : unitary_group n) = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas

noncomputable instance : group (unitary_group n) :=
{ mul_assoc := λ A B C, subtype.eq (A.val.mul_assoc B.val C.val),
  one_mul := λ M, subtype.eq $ one_mul _,
  mul_one := λ M, subtype.eq $ mul_one _,
  mul_left_inv := λ A, subtype.eq A.2,
  ..unitary_group.has_mul,
  ..unitary_group.has_inv,
  ..unitary_group.has_one }

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
noncomputable def to_linear_equiv (A : unitary_group n) : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) :=
{ inv_fun := A⁻¹.to_lin',
  left_inv := λ x, calc
    A⁻¹.to_lin'.comp A.to_lin' x
        = (A⁻¹ * A).to_lin' x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_left_inv, to_lin'_one, id_apply],
  right_inv := λ x, calc
    A.to_lin'.comp A⁻¹.to_lin' x
        = (A * A⁻¹).to_lin' x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_right_inv, to_lin'_one, id_apply],
  ..matrix.to_lin' A }

/-- `to_GL` is the map from the unitary group to the general linear group -/
noncomputable def to_GL (A : unitary_group n) : general_linear_group ℂ (n → ℂ) :=
general_linear_group.of_linear_equiv (to_linear_equiv A)

lemma coe_to_GL (A : unitary_group n) :
  (@coe (units _) _ _ (to_GL A)) = A.to_lin' :=
rfl

@[simp]
lemma to_GL_one : to_GL (1 : unitary_group n) = 1 :=
by { ext1 v i, rw [coe_to_GL, to_lin'_one], refl }

@[simp]
lemma to_GL_mul (A B : unitary_group n) :
  to_GL (A * B) = to_GL A * to_GL B :=
by { ext1 v i, rw [coe_to_GL, to_lin'_mul], refl }

/-- `unitary_group.embedding_GL` is the embedding from `unitary_group n`
  to `general_linear_group n ℂ`. -/
noncomputable def embedding_GL : (unitary_group n) →* (general_linear_group ℂ (n → ℂ)) :=
⟨λ A, to_GL A, by simp, by simp⟩

end unitary_group

end matrix
