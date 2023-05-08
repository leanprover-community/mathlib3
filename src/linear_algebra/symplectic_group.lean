/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery
-/

import linear_algebra.matrix.nonsingular_inverse

/-!
# The Symplectic Group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the symplectic group and proves elementary properties.

## Main Definitions

`matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
`symplectic_group`: the group of symplectic matrices

## TODO
* Every symplectic matrix has determinant 1.
* For `n = 1` the symplectic group coincides with the special linear group.
-/

open_locale matrix

variables {l R : Type*}

namespace matrix

variables (l) [decidable_eq l] (R) [comm_ring R]

section J_matrix_lemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : matrix (l ⊕ l) (l ⊕ l) R := matrix.from_blocks 0 (-1) 1 0

@[simp] lemma J_transpose : (J l R)ᵀ = - (J l R) :=
begin
  rw [J, from_blocks_transpose, ←neg_one_smul R (from_blocks _ _ _ _), from_blocks_smul,
    matrix.transpose_zero, matrix.transpose_one, transpose_neg],
  simp [from_blocks],
end

variables [fintype l]

lemma J_squared : (J l R) ⬝ (J l R) = -1 :=
begin
  rw [J, from_blocks_multiply],
  simp only [matrix.zero_mul, matrix.neg_mul, zero_add, neg_zero, matrix.one_mul, add_zero],
  rw [← neg_zero, ← matrix.from_blocks_neg, ← from_blocks_one],
end

lemma J_inv : (J l R)⁻¹ = -(J l R) :=
begin
  refine matrix.inv_eq_right_inv _,
  rw [matrix.mul_neg, J_squared],
  exact neg_neg 1,
end

lemma J_det_mul_J_det : (det (J l R)) * (det (J l R)) = 1 :=
begin
  rw [←det_mul, J_squared],
  rw [←one_smul R (-1 : matrix _ _ R)],
  rw [smul_neg, ←neg_smul, det_smul],
  simp only [fintype.card_sum, det_one, mul_one],
  apply even.neg_one_pow,
  exact even_add_self _
end

lemma is_unit_det_J : is_unit (det (J l R)) :=
is_unit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

end J_matrix_lemmas

variable [fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
def symplectic_group : submonoid (matrix (l ⊕ l) (l ⊕ l)  R) :=
{ carrier := { A | A ⬝ (J l R) ⬝ Aᵀ = J l R},
  mul_mem' :=
  begin
    intros a b ha hb,
    simp only [mul_eq_mul, set.mem_set_of_eq, transpose_mul] at *,
    rw [←matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb],
    exact ha,
  end,
  one_mem' := by simp }

end matrix

namespace symplectic_group

variables {l} {R} [decidable_eq l] [fintype l] [comm_ring R]

open matrix

lemma mem_iff {A : matrix (l ⊕ l) (l ⊕ l)  R} :
  A ∈ symplectic_group l R ↔ A ⬝ (J l R) ⬝ Aᵀ = J l R :=
by simp [symplectic_group]

instance coe_matrix : has_coe (symplectic_group l R) (matrix (l ⊕ l) (l ⊕ l)  R)
:= by apply_instance

section symplectic_J

variables (l) (R)

lemma J_mem : (J l R) ∈ symplectic_group l R :=
begin
  rw [mem_iff, J, from_blocks_multiply, from_blocks_transpose, from_blocks_multiply],
  simp,
end

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
def sym_J : symplectic_group l R := ⟨J l R, J_mem l R⟩

variables {l} {R}

@[simp] lemma coe_J : ↑(sym_J l R) = J l R := rfl

end symplectic_J

variables {R} {A : matrix (l ⊕ l) (l ⊕ l) R}

lemma neg_mem (h : A ∈ symplectic_group l R) : -A ∈ symplectic_group l R :=
begin
  rw mem_iff at h ⊢,
  simp [h],
end

lemma symplectic_det (hA : A ∈ symplectic_group l R) : is_unit $ det A :=
begin
  rw is_unit_iff_exists_inv,
  use A.det,
  refine (is_unit_det_J l R).mul_left_cancel _,
  rw [mul_one],
  rw mem_iff at hA,
  apply_fun det at hA,
  simp only [det_mul, det_transpose] at hA,
  rw [mul_comm A.det, mul_assoc] at hA,
  exact hA,
end

lemma transpose_mem (hA : A ∈ symplectic_group l R) :
  Aᵀ ∈ symplectic_group l R :=
begin
  rw mem_iff at ⊢ hA,
  rw transpose_transpose,
  have huA := symplectic_det hA,
  have huAT : is_unit (Aᵀ).det :=
  begin
    rw matrix.det_transpose,
    exact huA,
  end,
  calc Aᵀ ⬝ J l R ⬝ A
      = - Aᵀ ⬝ (J l R)⁻¹ ⬝ A  : by {rw J_inv, simp}
  ... = - Aᵀ ⬝ (A ⬝ J l R ⬝ Aᵀ)⁻¹ ⬝ A : by rw hA
  ... = - (Aᵀ ⬝ (Aᵀ⁻¹ ⬝ (J l R)⁻¹)) ⬝ A⁻¹ ⬝ A : by simp only [matrix.mul_inv_rev,
                                                              matrix.mul_assoc, matrix.neg_mul]
  ... = - (J l R)⁻¹ : by rw [mul_nonsing_inv_cancel_left _ _ huAT,
                             nonsing_inv_mul_cancel_right _ _ huA]
  ... = (J l R) : by simp [J_inv]
end

@[simp] lemma transpose_mem_iff : Aᵀ ∈ symplectic_group l R ↔ A ∈ symplectic_group l R :=
⟨λ hA, by simpa using transpose_mem hA , transpose_mem⟩

lemma mem_iff' : A ∈ symplectic_group l R ↔ Aᵀ ⬝ (J l R) ⬝ A = J l R :=
by rw [←transpose_mem_iff, mem_iff, transpose_transpose]

instance : has_inv (symplectic_group l R) :=
{ inv := λ A, ⟨- (J l R) ⬝ (A : matrix (l ⊕ l) (l ⊕ l) R)ᵀ ⬝ (J l R),
  mul_mem (mul_mem (neg_mem $ J_mem _ _) $ transpose_mem A.2) $ J_mem _ _⟩ }

lemma coe_inv (A : symplectic_group l R) :
  (↑(A⁻¹) : matrix _ _ _) = - J l R ⬝ (↑A)ᵀ ⬝ J l R := rfl

lemma inv_left_mul_aux (hA : A ∈ symplectic_group l R) :
  -(J l R ⬝ Aᵀ ⬝ J l R ⬝ A) = 1 :=
calc -(J l R ⬝ Aᵀ ⬝ J l R ⬝ A)
    = - J l R ⬝ (Aᵀ ⬝ J l R ⬝ A) : by simp only [matrix.mul_assoc, matrix.neg_mul]
... = - J l R ⬝ J l R : by {rw mem_iff' at hA, rw hA}
... = (-1 : R) • (J l R ⬝ J l R) : by simp only [matrix.neg_mul, neg_smul, one_smul]
... = (-1 : R) • -1 : by rw J_squared
... = 1 : by simp only [neg_smul_neg, one_smul]

lemma coe_inv' (A : symplectic_group l R) : (↑(A⁻¹) : matrix (l ⊕ l) (l ⊕ l) R) = A⁻¹ :=
begin
  refine (coe_inv A).trans (inv_eq_left_inv _).symm,
  simp [inv_left_mul_aux, coe_inv],
end

lemma inv_eq_symplectic_inv (A : matrix (l ⊕ l) (l ⊕ l) R) (hA : A ∈ symplectic_group l R) :
  A⁻¹ = - (J l R) ⬝ Aᵀ ⬝ (J l R) :=
inv_eq_left_inv (by simp only [matrix.neg_mul, inv_left_mul_aux hA])

instance : group (symplectic_group l R) :=
{ mul_left_inv := λ A,
  begin
    apply subtype.ext,
    simp only [submonoid.coe_one, submonoid.coe_mul, matrix.neg_mul, coe_inv],
    rw [matrix.mul_eq_mul, matrix.neg_mul],
    exact inv_left_mul_aux A.2,
  end,
  .. symplectic_group.has_inv,
  .. submonoid.to_monoid _ }

end symplectic_group
