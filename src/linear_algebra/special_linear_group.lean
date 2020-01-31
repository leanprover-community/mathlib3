/-
  Copyright (c) 2020 Anne Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Anne Baanen.

  The Special Linear group `special_linear_group(n, R)`.
-/
import linear_algebra.basic
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse
import tactic.norm_cast

/-!
# The Special Linear group `special_linear_group(n, R)`

This file defines the elements of the Special Linear group `special_linear_group n R`,
also written `special_linear_group(n, R)` or `SLₙ(R)`, consisting of all `n` by `n`
`R`-matrices with determinant `1`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map

set_option class.instance_max_depth 60

section

variables (n : Type u) [fintype n] [decidable_eq n] (R : Type v) [comm_ring R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1. -/
def special_linear_group := { A : matrix n n R // A.det = 1 }

end

namespace special_linear_group

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

lemma ext_iff (A B : special_linear_group n R) : A = B ↔ (∀ i j, A.1 i j = B.1 i j) :=
iff.trans subtype.ext ⟨(λ h i j, by rw h), matrix.ext⟩

@[ext]
lemma ext (A B : special_linear_group n R) : (∀ i j, A.1 i j = B.1 i j) → A = B :=
(special_linear_group.ext_iff A B).mpr

instance has_inv : has_inv (special_linear_group n R) := ⟨λ A, ⟨adjugate A.1, det_adjugate_eq_one A.2⟩⟩

instance has_mul : has_mul (special_linear_group n R) :=
⟨λ A B, ⟨A.1 ⬝ B.1, by rw [det_mul, A.2, B.2, one_mul]⟩⟩

instance has_one : has_one (special_linear_group n R) := ⟨⟨1, det_one⟩⟩

instance : inhabited (special_linear_group n R) := ⟨1⟩

@[simp] lemma inv_val (A : special_linear_group n R) : A⁻¹.val = adjugate A.val := rfl

@[simp] lemma mul_val (A B : special_linear_group n R) : (A * B).val = A.val ⬝ B.val := rfl

@[simp] lemma one_val : (1 : special_linear_group n R).val = 1 := rfl

instance group : group (special_linear_group n R) :=
{ mul_assoc := λ A B C, by { ext, simp [mul_val, matrix.mul_assoc] },
  one_mul := λ A, by { ext, simp },
  mul_one := λ A, by { ext, simp },
  mul_left_inv := λ A, by { ext, simp [adjugate_mul, A.2] },
  ..special_linear_group.has_mul,
  ..special_linear_group.has_one,
  ..special_linear_group.has_inv,
}

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A.val`, as a linear equivalence. -/
def to_linear_equiv (A : special_linear_group n R) : (n → R) ≃ₗ[R] (n → R) :=
{ inv_fun := A⁻¹.val.to_lin,
  left_inv := λ x, calc
    (A⁻¹.val.to_lin.comp A.val.to_lin) x
        = ((A⁻¹ * A).val.to_lin : (n → R) → (n → R)) x : by rw [←mul_to_lin, mul_val]
    ... = x : by simp,
  right_inv := λ x, calc
    (A.val.to_lin.comp A⁻¹.val.to_lin) x
        = ((A * A⁻¹).val.to_lin : (n → R) → (n → R)) x : by rw [←mul_to_lin, mul_val]
    ... = x : by simp,
  ..A.val.to_lin
}

instance coe_GL : has_coe (special_linear_group n R) (general_linear_group R (n → R)) :=
⟨λ A, general_linear_group.of_linear_equiv (to_linear_equiv A)⟩

lemma coe_coe (A : special_linear_group n R) :
  (@coe (units _) _ _ (A : general_linear_group R (n → R))) = A.val.to_lin := rfl

@[simp, elim_cast]
lemma coe_GL_one : ((1 : special_linear_group n R) : general_linear_group R (n → R)) = 1 :=
by { ext v i, rw [coe_coe, one_val, to_lin_one], refl }

@[simp, move_cast]
lemma coe_GL_mul (A B : special_linear_group n R) :
  (↑(A * B) : general_linear_group R (n → R)) = ↑A * ↑B :=
by { ext v i, rw [coe_coe, mul_val, mul_to_lin], refl }

/-- `special_linear_group.to_GL` is the embedding from `special_linear_group n R`
  to `general_linear_group n R`. -/
def to_GL : (special_linear_group n R) →* (general_linear_group R (n → R)) :=
⟨λ A, ↑A, by norm_cast, by { intros, norm_cast }⟩

end special_linear_group

end matrix
