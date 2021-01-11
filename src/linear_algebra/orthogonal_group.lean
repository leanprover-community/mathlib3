/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Shing Tak Lam
-/
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse
import data.real.basic

/-!
# The Orthogonal Group O(n)

This file defines elements of the orthogonal group `orthogonal_group n`, also written `O(n)`,
consisting of all `n` by `n` real matrices where the transpose is the inverse. In addition,
we define the group structure on `orthogonal_group n` and the embedding into the general linear
group `general_linear_group ℝ (n → ℝ)`.

## Main Definitions

 * `matrix.orthogonal_group` is the type of matrices where the transpose is the inverse
 * `matrix.orthogonal_group.group` is the group structure (under multiplication)
 * `matrix.orthogonal_group.embedding_GL` is the embedding `O(n) → GLₙ(ℝ)`

## References

 * https://en.wikipedia.org/wiki/Orthogonal_group

## Tags

matrix group, group, orthogonal group

-/

namespace matrix

universe u
open_locale matrix
open linear_map

section

variables (n : Type u) [fintype n] [decidable_eq n]

/-- `orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse. -/
def orthogonal_group := {M : matrix n n ℝ // matrix.mul Mᵀ M = 1}

end

namespace orthogonal_group

variables {n : Type u} [decidable_eq n] [fintype n]

instance coe_matrix : has_coe (orthogonal_group n) (matrix n n ℝ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (orthogonal_group n) :=
{ F   := λ _, n → n → ℝ,
  coe := λ A, A.val }

/--
  `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

  After the group structure on `orthogonal_group n` is defined,
  we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : orthogonal_group n) := matrix.to_lin' A

lemma ext_iff (A B : orthogonal_group n) : A = B ↔ ∀ i j, A i j = B i j :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : orthogonal_group n) : (∀ i j, A i j = B i j) → A = B :=
(orthogonal_group.ext_iff A B).mpr

instance : has_inv (orthogonal_group n) :=
⟨λ A, ⟨Aᵀ, matrix.nonsing_inv_left_right _ _ $ by { rw matrix.transpose_transpose, exact A.2 }⟩⟩

instance : has_mul (orthogonal_group n) :=
⟨λ A B, ⟨A.1 ⬝ B.1, begin
    rw matrix.transpose_mul,
    rw [←matrix.mul_assoc, matrix.mul_assoc _ _ A.1, A.2, matrix.mul_one, B.2],
  end⟩⟩

instance : has_one (orthogonal_group n) :=
⟨⟨1, by rw [matrix.transpose_one, matrix.one_mul]⟩⟩

instance : inhabited (orthogonal_group n) := ⟨1⟩

section coe_lemmas

variables (A B : orthogonal_group n)

@[simp] lemma inv_val : ↑(A⁻¹) = Aᵀ := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = Aᵀ := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : orthogonal_group n) = (1 : matrix n n ℝ) := rfl

@[simp] lemma one_apply : ⇑(1 : orthogonal_group n) = (1 : matrix n n ℝ) := rfl

@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : orthogonal_group n) = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas

instance : group (orthogonal_group n) :=
{ mul_assoc := λ A B C, subtype.eq (A.val.mul_assoc B.val C.val),
  one_mul := λ M, subtype.eq $ one_mul _,
  mul_one := λ M, subtype.eq $ mul_one _,
  mul_left_inv := λ U, subtype.eq U.2,
  ..orthogonal_group.has_mul,
  ..orthogonal_group.has_one,
  ..orthogonal_group.has_inv }

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : orthogonal_group n) : (n → ℝ) ≃ₗ[ℝ] (n → ℝ) :=
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

/-- `to_GL` is the map from the orthogonal group to the general linear group -/
def to_GL (A : orthogonal_group n) : general_linear_group ℝ (n → ℝ) :=
general_linear_group.of_linear_equiv (to_linear_equiv A)

lemma coe_to_GL (A : orthogonal_group n) :
  (@coe (units _) _ _ (to_GL A)) = A.to_lin' :=
rfl

@[simp]
lemma to_GL_one : to_GL (1 : orthogonal_group n) = 1 :=
by { ext v i, rw [coe_to_GL, to_lin'_one], refl }

@[simp]
lemma to_GL_mul (A B : orthogonal_group n) :
  to_GL (A * B) = to_GL A * to_GL B :=
by { ext v i, rw [coe_to_GL, to_lin'_mul], refl }

/-- `orthogonal_group.embedding_GL` is the embedding from `orthogonal_group n`
  to `general_linear_group n ℝ`. -/
def embedding_GL : (orthogonal_group n) →* (general_linear_group ℝ (n → ℝ)) :=
⟨λ A, to_GL A, by simp, by simp⟩

end orthogonal_group

end matrix
