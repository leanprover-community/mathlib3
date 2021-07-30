/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import linear_algebra.matrix
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.special_linear_group
import linear_algebra.determinant

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.


## Main definitions

 * `matrix.general_linear_group` is the type of matrices over R which are units in the matrix ring.
 * `matrix.GL_plus.GL_pos` gives the subgroup of matrices with
 positive determinant (over a linear ordered ring)

## Implementation notes


## References


## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map

section

variables (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [comm_ring R]

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbreviation general_linear_group (R : Type*) [comm_ring R] : Type* := units (matrix n n R)

notation `GL` := general_linear_group

lemma GL.is_unit_det  (A : GL n R) : is_unit ((A : matrix n n R).det) :=
begin
  rw ←matrix.is_unit_iff_is_unit_det,
  exact units.is_unit _
end

end
namespace general_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

/--The `GL n R` and `general_linear_group R n` groups are multiplicatively equivalent-/
def to_lin : (GL n R) ≃* (linear_map.general_linear_group R (n → R)) :=
units.map_equiv to_lin_alg_equiv'.to_mul_equiv

/--Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : matrix n n R) (h : invertible (det A)) : GL n R :=
unit_of_det_invertible A

/--Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : matrix n n R) (h : is_unit (det A)) : GL n R :=
nonsing_inv_unit A h

instance coe_fun : has_coe_to_fun (GL n R) :=
{ F   := λ _, n → n → R,
  coe := λ A, A.val }

lemma ext_iff (A B : GL n R) : A = B ↔ (∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :=
units.ext_iff.trans matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
lemma ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :
  A = B :=
units.ext $ matrix.ext h

section coe_lemmas

variables (A B : GL n R)

@[simp] lemma coe_fn_eq_coe : ⇑A = (↑A : matrix n n R) := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma one_val : ↑(1 : GL n R) = (1 : matrix n n R) := rfl

@[simp] lemma coe_inv : ↑(A⁻¹) = (↑A : matrix n n R)⁻¹ :=
begin
  letI := A.invertible,
  exact inv_eq_nonsing_inv_of_invertible (↑A : matrix n n R),
end

@[simp] lemma to_lin'_mul : to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one : to_lin' (1 : GL n R).1 = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas

instance SL_to_GL : has_coe (special_linear_group n R) (GL n R) :=
⟨λ A, ⟨↑A, ↑(A⁻¹), congr_arg coe (mul_right_inv A), congr_arg coe (mul_left_inv A)⟩⟩

lemma det_not_zero [nontrivial R] (A : GL n R) : det A ≠ 0 :=
begin
  have := GL.is_unit_det _ _ A, simp,
  by_contradiction,
  unfold_coes at *,
  rw h at this,
  simp at *,
  exact this,
end

end general_linear_group

namespace GL_plus

variables  (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [linear_ordered_comm_ring R ]

lemma one_in_GL_pos : 0 < det (1 : GL n R) :=
begin
simp only [det_one, general_linear_group.coe_fn_eq_coe, general_linear_group.one_val, zero_lt_one],
end

lemma mul_in_GL_pos (A B : GL n R) (h1 : 0 < det A) (h2 : 0 < det B) : 0 < det (A*B) :=
begin
  simp only [gt_iff_lt, det_mul, mul_eq_mul],
  apply mul_pos h1 h2,
end

lemma inv_det_pos  (A : GL n R) (h : 0 < det A) :  0 < det (A⁻¹).1 :=
begin
  have h0 := (GL.is_unit_det _ _ A),
  have h1 := is_unit_nonsing_inv_det A h0,
  have h2 := nonsing_inv_det A h0,
  have h3 : 0 < det ⇑A*  det (⇑A)⁻¹ , by {rw mul_comm, rw h2, linarith},
  unfold_coes at *,
  convert (zero_lt_mul_left h).mp h3,
  have := general_linear_group.coe_inv A,
  unfold_coes  at this,
  simp_rw this,
end

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GL_pos : subgroup (GL n R) :=
{ carrier := {M  | 0 < det M},
  one_mem' := one_in_GL_pos _ _ ,
  mul_mem' := λ A B h1 h2, mul_in_GL_pos _ _ A B h1 h2,
  inv_mem' := λ A h1, begin
    have:= inv_det_pos _ _ A h1,
    simp only [set.mem_set_of_eq] at *,
    unfold_coes at *,
    convert this,
  end }

@[simp] lemma mem_GL_pos (A : GL n R) : A  ∈ (GL_pos n R)  ↔ 0 < A.1.det := iff.rfl

lemma SL_det_pos' (A : special_linear_group n R) : 0 < (A).1.det :=
begin
  have := A.2, simp only [gt_iff_lt, subtype.val_eq_coe],
  simp only [subtype.val_eq_coe] at this,
  rw this,
  linarith,
end

instance SL_to_GL_pos : has_coe (special_linear_group n R) (GL_pos n R) :=
⟨λ A, ⟨(A : GL n R), by {simp, apply SL_det_pos' _ _ A}, ⟩⟩

end GL_plus
end matrix
