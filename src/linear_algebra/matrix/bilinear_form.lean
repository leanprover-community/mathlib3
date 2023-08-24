/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/

import linear_algebra.matrix.basis
import linear_algebra.matrix.nondegenerate
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.bilinear_form
import linear_algebra.matrix.sesquilinear_form

/-!
# Bilinear form

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the conversion between bilinear forms and matrices.

## Main definitions

 * `matrix.to_bilin` given a basis define a bilinear form
 * `matrix.to_bilin'` define the bilinear form on `n → R`
 * `bilin_form.to_matrix`: calculate the matrix coefficients of a bilinear form
 * `bilin_form.to_matrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notations

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## Tags

bilinear_form, matrix, basis

-/

variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M]
variables {R₁ : Type*} {M₁ : Type*} [ring R₁] [add_comm_group M₁] [module R₁ M₁]
variables {R₂ : Type*} {M₂ : Type*} [comm_semiring R₂] [add_comm_monoid M₂] [module R₂ M₂]
variables {R₃ : Type*} {M₃ : Type*} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃]
variables {V : Type*} {K : Type*} [field K] [add_comm_group V] [module K V]
variables {B : bilin_form R M} {B₁ : bilin_form R₁ M₁} {B₂ : bilin_form R₂ M₂}

section matrix
variables {n o : Type*}

open_locale big_operators
open bilin_form finset linear_map matrix
open_locale matrix

/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def matrix.to_bilin'_aux [fintype n] (M : matrix n n R₂) : bilin_form R₂ (n → R₂) :=
{ bilin := λ v w, ∑ i j, v i * M i j * w j,
  bilin_add_left := λ x y z, by simp only [pi.add_apply, add_mul, sum_add_distrib],
  bilin_smul_left := λ a x y, by simp only [pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum],
  bilin_add_right := λ x y z, by simp only [pi.add_apply, mul_add, sum_add_distrib],
  bilin_smul_right := λ a x y,
    by simp only [pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_sum] }

lemma matrix.to_bilin'_aux_std_basis [fintype n] [decidable_eq n] (M : matrix n n R₂)
  (i j : n) : M.to_bilin'_aux (std_basis R₂ (λ _, R₂) i 1) (std_basis R₂ (λ _, R₂) j 1) = M i j :=
begin
  rw [matrix.to_bilin'_aux, coe_fn_mk, sum_eq_single i, sum_eq_single j],
  { simp only [std_basis_same, std_basis_same, one_mul, mul_one] },
  { rintros j' - hj',
    apply mul_eq_zero_of_right,
    exact std_basis_ne R₂ (λ _, R₂) _ _ hj' 1 },
  { intros,
    have := finset.mem_univ j,
    contradiction },
  { rintros i' - hi',
    refine finset.sum_eq_zero (λ j _, _),
    apply mul_eq_zero_of_left,
    apply mul_eq_zero_of_left,
    exact std_basis_ne R₂ (λ _, R₂) _ _ hi' 1 },
  { intros,
    have := finset.mem_univ i,
    contradiction }
end

/-- The linear map from bilinear forms to `matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def bilin_form.to_matrix_aux (b : n → M₂) : bilin_form R₂ M₂ →ₗ[R₂] matrix n n R₂ :=
{ to_fun := λ B, of $ λ i j, B (b i) (b j),
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl }

@[simp] lemma bilin_form.to_matrix_aux_apply (B : bilin_form R₂ M₂) (b : n → M₂) (i j : n) :
  bilin_form.to_matrix_aux b B i j = B (b i) (b j) := rfl

variables [fintype n] [fintype o]

lemma to_bilin'_aux_to_matrix_aux [decidable_eq n] (B₂ : bilin_form R₂ (n → R₂)) :
  matrix.to_bilin'_aux (bilin_form.to_matrix_aux (λ j, std_basis R₂ (λ _, R₂) j 1) B₂) = B₂ :=
begin
  refine ext_basis (pi.basis_fun R₂ n) (λ i j, _),
  rw [pi.basis_fun_apply, pi.basis_fun_apply, matrix.to_bilin'_aux_std_basis,
    bilin_form.to_matrix_aux_apply]
end

section to_matrix'

/-! ### `to_matrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/

variables [decidable_eq n] [decidable_eq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def bilin_form.to_matrix' : bilin_form R₂ (n → R₂) ≃ₗ[R₂] matrix n n R₂ :=
{ inv_fun := matrix.to_bilin'_aux,
  left_inv := by convert to_bilin'_aux_to_matrix_aux,
  right_inv := λ M,
    by { ext i j, simp only [to_fun_eq_coe, bilin_form.to_matrix_aux_apply,
      matrix.to_bilin'_aux_std_basis] },
  ..bilin_form.to_matrix_aux (λ j, std_basis R₂ (λ _, R₂) j 1) }

@[simp] lemma bilin_form.to_matrix_aux_std_basis (B : bilin_form R₂ (n → R₂)) :
  bilin_form.to_matrix_aux (λ j, std_basis R₂ (λ _, R₂) j 1) B =
    bilin_form.to_matrix' B :=
rfl

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def matrix.to_bilin' : matrix n n R₂ ≃ₗ[R₂] bilin_form R₂ (n → R₂) :=
bilin_form.to_matrix'.symm

@[simp] lemma matrix.to_bilin'_aux_eq (M : matrix n n R₂) :
  matrix.to_bilin'_aux M = matrix.to_bilin' M :=
rfl

lemma matrix.to_bilin'_apply (M : matrix n n R₂) (x y : n → R₂) :
  matrix.to_bilin' M x y = ∑ i j, x i * M i j * y j := rfl

lemma matrix.to_bilin'_apply' (M : matrix n n R₂) (v w : n → R₂) :
  matrix.to_bilin' M v w = matrix.dot_product v (M.mul_vec w) :=
begin
  simp_rw [matrix.to_bilin'_apply, matrix.dot_product,
           matrix.mul_vec, matrix.dot_product],
  refine finset.sum_congr rfl (λ _ _, _),
  rw finset.mul_sum,
  refine finset.sum_congr rfl (λ _ _, _),
  rw ← mul_assoc,
end

@[simp] lemma matrix.to_bilin'_std_basis (M : matrix n n R₂) (i j : n) :
  matrix.to_bilin' M (std_basis R₂ (λ _, R₂) i 1) (std_basis R₂ (λ _, R₂) j 1) =
    M i j :=
matrix.to_bilin'_aux_std_basis M i j

@[simp] lemma bilin_form.to_matrix'_symm :
  (bilin_form.to_matrix'.symm : matrix n n R₂ ≃ₗ[R₂] _) = matrix.to_bilin' :=
rfl

@[simp] lemma matrix.to_bilin'_symm :
  (matrix.to_bilin'.symm : _ ≃ₗ[R₂] matrix n n R₂) = bilin_form.to_matrix' :=
bilin_form.to_matrix'.symm_symm

@[simp] lemma matrix.to_bilin'_to_matrix' (B : bilin_form R₂ (n → R₂)) :
  matrix.to_bilin' (bilin_form.to_matrix' B) = B :=
matrix.to_bilin'.apply_symm_apply B

@[simp] lemma bilin_form.to_matrix'_to_bilin' (M : matrix n n R₂) :
  bilin_form.to_matrix' (matrix.to_bilin' M) = M :=
bilin_form.to_matrix'.apply_symm_apply M

@[simp] lemma bilin_form.to_matrix'_apply (B : bilin_form R₂ (n → R₂)) (i j : n) :
  bilin_form.to_matrix' B i j =
    B (std_basis R₂ (λ _, R₂) i 1) (std_basis R₂ (λ _, R₂) j 1) :=
rfl

@[simp] lemma bilin_form.to_matrix'_comp (B : bilin_form R₂ (n → R₂))
  (l r : (o → R₂) →ₗ[R₂] (n → R₂)) :
  (B.comp l r).to_matrix' = l.to_matrix'ᵀ ⬝ B.to_matrix' ⬝ r.to_matrix' :=
begin
  ext i j,
  simp only [bilin_form.to_matrix'_apply, bilin_form.comp_apply, transpose_apply, matrix.mul_apply,
    linear_map.to_matrix', linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ← bilin_form.sum_repr_mul_repr_mul (pi.basis_fun R₂ n) (l _) (r _) },
  rw finsupp.sum_fintype,
  { apply sum_congr rfl,
    rintros i' -,
    rw finsupp.sum_fintype,
    { apply sum_congr rfl,
      rintros j' -,
      simp only [smul_eq_mul, pi.basis_fun_repr, mul_assoc, mul_comm, mul_left_comm,
                 pi.basis_fun_apply, of_apply] },
    { intros, simp only [zero_smul, smul_zero] } },
  { intros, simp only [zero_smul, finsupp.sum_zero] }
end

lemma bilin_form.to_matrix'_comp_left (B : bilin_form R₂ (n → R₂))
  (f : (n → R₂) →ₗ[R₂] (n → R₂)) : (B.comp_left f).to_matrix' = f.to_matrix'ᵀ ⬝ B.to_matrix' :=
by simp only [bilin_form.comp_left, bilin_form.to_matrix'_comp, to_matrix'_id, matrix.mul_one]

lemma bilin_form.to_matrix'_comp_right (B : bilin_form R₂ (n → R₂))
  (f : (n → R₂) →ₗ[R₂] (n → R₂)) : (B.comp_right f).to_matrix' = B.to_matrix' ⬝ f.to_matrix' :=
by simp only [bilin_form.comp_right, bilin_form.to_matrix'_comp, to_matrix'_id,
              transpose_one, matrix.one_mul]

lemma bilin_form.mul_to_matrix'_mul (B : bilin_form R₂ (n → R₂))
  (M : matrix o n R₂) (N : matrix n o R₂) :
  M ⬝ B.to_matrix' ⬝ N = (B.comp Mᵀ.to_lin' N.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp, transpose_transpose, to_matrix'_to_lin']

lemma bilin_form.mul_to_matrix' (B : bilin_form R₂ (n → R₂)) (M : matrix n n R₂) :
  M ⬝ B.to_matrix' = (B.comp_left Mᵀ.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp_left, transpose_transpose, to_matrix'_to_lin']

lemma bilin_form.to_matrix'_mul (B : bilin_form R₂ (n → R₂)) (M : matrix n n R₂) :
  B.to_matrix' ⬝ M = (B.comp_right M.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp_right, to_matrix'_to_lin']

lemma matrix.to_bilin'_comp (M : matrix n n R₂) (P Q : matrix n o R₂) :
  M.to_bilin'.comp P.to_lin' Q.to_lin' = (Pᵀ ⬝ M ⬝ Q).to_bilin' :=
bilin_form.to_matrix'.injective
  (by simp only [bilin_form.to_matrix'_comp, bilin_form.to_matrix'_to_bilin', to_matrix'_to_lin'])

end to_matrix'

section to_matrix

/-! ### `to_matrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/

variables [decidable_eq n] (b : basis n R₂ M₂)

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def bilin_form.to_matrix : bilin_form R₂ M₂ ≃ₗ[R₂] matrix n n R₂ :=
(bilin_form.congr b.equiv_fun).trans bilin_form.to_matrix'

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def matrix.to_bilin : matrix n n R₂ ≃ₗ[R₂] bilin_form R₂ M₂ :=
(bilin_form.to_matrix b).symm

@[simp] lemma bilin_form.to_matrix_apply (B : bilin_form R₂ M₂) (i j : n) :
  bilin_form.to_matrix b B i j = B (b i) (b j) :=
by rw [bilin_form.to_matrix, linear_equiv.trans_apply, bilin_form.to_matrix'_apply, congr_apply,
       b.equiv_fun_symm_std_basis, b.equiv_fun_symm_std_basis]

@[simp] lemma matrix.to_bilin_apply (M : matrix n n R₂) (x y : M₂) :
  matrix.to_bilin b M x y = ∑ i j, b.repr x i * M i j * b.repr y j :=
begin
  rw [matrix.to_bilin, bilin_form.to_matrix, linear_equiv.symm_trans_apply, ← matrix.to_bilin'],
  simp only [congr_symm, congr_apply, linear_equiv.symm_symm, matrix.to_bilin'_apply,
    basis.equiv_fun_apply]
end

-- Not a `simp` lemma since `bilin_form.to_matrix` needs an extra argument
lemma bilinear_form.to_matrix_aux_eq (B : bilin_form R₂ M₂) :
  bilin_form.to_matrix_aux b B = bilin_form.to_matrix b B :=
ext (λ i j, by rw [bilin_form.to_matrix_apply, bilin_form.to_matrix_aux_apply])

@[simp] lemma bilin_form.to_matrix_symm :
  (bilin_form.to_matrix b).symm = matrix.to_bilin b :=
rfl

@[simp] lemma matrix.to_bilin_symm :
  (matrix.to_bilin b).symm = bilin_form.to_matrix b :=
(bilin_form.to_matrix b).symm_symm

lemma matrix.to_bilin_basis_fun :
  matrix.to_bilin (pi.basis_fun R₂ n) = matrix.to_bilin' :=
by { ext M, simp only [matrix.to_bilin_apply, matrix.to_bilin'_apply, pi.basis_fun_repr] }

lemma bilin_form.to_matrix_basis_fun :
  bilin_form.to_matrix (pi.basis_fun R₂ n) = bilin_form.to_matrix' :=
by { ext B, rw [bilin_form.to_matrix_apply, bilin_form.to_matrix'_apply,
                pi.basis_fun_apply, pi.basis_fun_apply] }

@[simp] lemma matrix.to_bilin_to_matrix (B : bilin_form R₂ M₂) :
  matrix.to_bilin b (bilin_form.to_matrix b B) = B :=
(matrix.to_bilin b).apply_symm_apply B

@[simp] lemma bilin_form.to_matrix_to_bilin (M : matrix n n R₂) :
  bilin_form.to_matrix b (matrix.to_bilin b M) = M :=
(bilin_form.to_matrix b).apply_symm_apply M

variables {M₂' : Type*} [add_comm_monoid M₂'] [module R₂ M₂']
variables (c : basis o R₂ M₂')
variables [decidable_eq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
lemma bilin_form.to_matrix_comp
  (B : bilin_form R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
  bilin_form.to_matrix c (B.comp l r) =
    (to_matrix c b l)ᵀ ⬝ bilin_form.to_matrix b B ⬝ to_matrix c b r :=
begin
  ext i j,
  simp only [bilin_form.to_matrix_apply, bilin_form.comp_apply, transpose_apply, matrix.mul_apply,
    linear_map.to_matrix', linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ← bilin_form.sum_repr_mul_repr_mul b },
  rw finsupp.sum_fintype,
  { apply sum_congr rfl,
    rintros i' -,
    rw finsupp.sum_fintype,
    { apply sum_congr rfl,
      rintros j' -,
      simp only [smul_eq_mul, linear_map.to_matrix_apply,
        basis.equiv_fun_apply, mul_assoc, mul_comm, mul_left_comm] },
    { intros, simp only [zero_smul, smul_zero] } },
  { intros, simp only [zero_smul, finsupp.sum_zero] }
end

lemma bilin_form.to_matrix_comp_left (B : bilin_form R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
  bilin_form.to_matrix b (B.comp_left f) = (to_matrix b b f)ᵀ ⬝ bilin_form.to_matrix b B :=
by simp only [comp_left, bilin_form.to_matrix_comp b b, to_matrix_id, matrix.mul_one]

lemma bilin_form.to_matrix_comp_right (B : bilin_form R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
  bilin_form.to_matrix b (B.comp_right f) = bilin_form.to_matrix b B ⬝ (to_matrix b b f) :=
by simp only [bilin_form.comp_right, bilin_form.to_matrix_comp b b, to_matrix_id,
              transpose_one, matrix.one_mul]

@[simp]
lemma bilin_form.to_matrix_mul_basis_to_matrix (c : basis o R₂ M₂) (B : bilin_form R₂ M₂) :
  (b.to_matrix c)ᵀ ⬝ bilin_form.to_matrix b B ⬝ b.to_matrix c = bilin_form.to_matrix c B :=
by rw [← linear_map.to_matrix_id_eq_basis_to_matrix, ← bilin_form.to_matrix_comp,
       bilin_form.comp_id_id]

lemma bilin_form.mul_to_matrix_mul (B : bilin_form R₂ M₂)
  (M : matrix o n R₂) (N : matrix n o R₂) :
  M ⬝ bilin_form.to_matrix b B ⬝ N =
    bilin_form.to_matrix c (B.comp (to_lin c b Mᵀ) (to_lin c b N)) :=
by simp only [B.to_matrix_comp b c, to_matrix_to_lin, transpose_transpose]

lemma bilin_form.mul_to_matrix (B : bilin_form R₂ M₂) (M : matrix n n R₂) :
  M ⬝ bilin_form.to_matrix b B =
    bilin_form.to_matrix b (B.comp_left (to_lin b b Mᵀ)) :=
by rw [B.to_matrix_comp_left b, to_matrix_to_lin, transpose_transpose]

lemma bilin_form.to_matrix_mul (B : bilin_form R₂ M₂) (M : matrix n n R₂) :
  bilin_form.to_matrix b B ⬝ M =
    bilin_form.to_matrix b (B.comp_right (to_lin b b M)) :=
by rw [B.to_matrix_comp_right b, to_matrix_to_lin]

lemma matrix.to_bilin_comp (M : matrix n n R₂) (P Q : matrix n o R₂) :
  (matrix.to_bilin b M).comp (to_lin c b P) (to_lin c b Q) = matrix.to_bilin c (Pᵀ ⬝ M ⬝ Q) :=
(bilin_form.to_matrix c).injective
  (by simp only [bilin_form.to_matrix_comp b c, bilin_form.to_matrix_to_bilin, to_matrix_to_lin])

end to_matrix

end matrix
section matrix_adjoints
open_locale matrix

variables {n : Type*} [fintype n]
variables (b : basis n R₃ M₃)
variables (J J₃ A A' : matrix n n R₃)

@[simp] lemma is_adjoint_pair_to_bilin' [decidable_eq n] :
  bilin_form.is_adjoint_pair (matrix.to_bilin' J) (matrix.to_bilin' J₃)
      (matrix.to_lin' A) (matrix.to_lin' A') ↔
    matrix.is_adjoint_pair J J₃ A A' :=
begin
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R₃ (n → R₃)), B = B' ↔
    (bilin_form.to_matrix' B) = (bilin_form.to_matrix' B'),
  { intros B B',
    split; intros h,
    { rw h },
    { exact bilin_form.to_matrix'.injective h } },
  rw [h, bilin_form.to_matrix'_comp_left, bilin_form.to_matrix'_comp_right,
      linear_map.to_matrix'_to_lin', linear_map.to_matrix'_to_lin',
      bilin_form.to_matrix'_to_bilin', bilin_form.to_matrix'_to_bilin'],
  refl,
end

@[simp] lemma is_adjoint_pair_to_bilin [decidable_eq n] :
  bilin_form.is_adjoint_pair (matrix.to_bilin b J) (matrix.to_bilin b J₃)
      (matrix.to_lin b b A) (matrix.to_lin b b A') ↔
    matrix.is_adjoint_pair J J₃ A A' :=
begin
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R₃ M₃), B = B' ↔
    (bilin_form.to_matrix b B) = (bilin_form.to_matrix b B'),
  { intros B B',
    split; intros h,
    { rw h },
    { exact (bilin_form.to_matrix b).injective h } },
  rw [h, bilin_form.to_matrix_comp_left, bilin_form.to_matrix_comp_right,
      linear_map.to_matrix_to_lin, linear_map.to_matrix_to_lin,
      bilin_form.to_matrix_to_bilin, bilin_form.to_matrix_to_bilin],
  refl,
end

lemma matrix.is_adjoint_pair_equiv' [decidable_eq n] (P : matrix n n R₃) (h : is_unit P) :
  (Pᵀ ⬝ J ⬝ P).is_adjoint_pair (Pᵀ ⬝ J ⬝ P) A A' ↔
    J.is_adjoint_pair J (P ⬝ A ⬝ P⁻¹) (P ⬝ A' ⬝ P⁻¹) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
begin
  let u := P.nonsing_inv_unit h',
  let v := Pᵀ.nonsing_inv_unit (P.is_unit_det_transpose h'),
  let x := Aᵀ * Pᵀ * J,
  let y := J * P * A',
  suffices : x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹,
  { dunfold matrix.is_adjoint_pair,
    repeat { rw matrix.transpose_mul, },
    simp only [←matrix.mul_eq_mul, ←mul_assoc, P.transpose_nonsing_inv],
    conv_lhs { to_rhs, rw [mul_assoc, mul_assoc], congr, skip, rw ←mul_assoc, },
    conv_rhs { rw [mul_assoc, mul_assoc], conv { to_lhs, congr, skip, rw ←mul_assoc }, },
    exact this, },
  rw units.eq_mul_inv_iff_mul_eq, conv_rhs { rw mul_assoc, }, rw v.inv_mul_eq_iff_eq_mul,
end

variables [decidable_eq n]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule' : submodule R₃ (matrix n n R₃) :=
(bilin_form.is_pair_self_adjoint_submodule (matrix.to_bilin' J) (matrix.to_bilin' J₃)).map
  ((linear_map.to_matrix' : ((n → R₃) →ₗ[R₃] (n → R₃)) ≃ₗ[R₃] matrix n n R₃) :
  ((n → R₃) →ₗ[R₃] (n → R₃)) →ₗ[R₃] matrix n n R₃)

lemma mem_pair_self_adjoint_matrices_submodule' :
  A ∈ (pair_self_adjoint_matrices_submodule J J₃) ↔ matrix.is_adjoint_pair J J₃ A A :=
by simp only [mem_pair_self_adjoint_matrices_submodule]

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule' : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule J J

lemma mem_self_adjoint_matrices_submodule' :
  A ∈ self_adjoint_matrices_submodule J ↔ J.is_self_adjoint A :=
by simp only [mem_self_adjoint_matrices_submodule]

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule' : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule (-J) J

lemma mem_skew_adjoint_matrices_submodule' :
  A ∈ skew_adjoint_matrices_submodule J ↔ J.is_skew_adjoint A :=
by simp only [mem_skew_adjoint_matrices_submodule]

end matrix_adjoints

namespace bilin_form


section det

open matrix

variables {A : Type*} [comm_ring A] [is_domain A] [module A M₃] (B₃ : bilin_form A M₃)
variables {ι : Type*} [decidable_eq ι] [fintype ι]

lemma _root_.matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin {M : matrix ι ι R₂}
  (b : basis ι R₂ M₂) : M.to_bilin'.nondegenerate ↔ (matrix.to_bilin b M).nondegenerate :=
(nondegenerate_congr_iff b.equiv_fun.symm).symm

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form

theorem _root_.matrix.nondegenerate.to_bilin' {M : matrix ι ι R₃} (h : M.nondegenerate) :
  M.to_bilin'.nondegenerate :=
λ x hx, h.eq_zero_of_ortho $ λ y, by simpa only [to_bilin'_apply'] using hx y

@[simp] lemma _root_.matrix.nondegenerate_to_bilin'_iff {M : matrix ι ι R₃} :
  M.to_bilin'.nondegenerate ↔ M.nondegenerate :=
⟨λ h v hv, h v $ λ w, (M.to_bilin'_apply' _ _).trans $ hv w, matrix.nondegenerate.to_bilin'⟩

theorem _root_.matrix.nondegenerate.to_bilin {M : matrix ι ι R₃} (h : M.nondegenerate)
  (b : basis ι R₃ M₃) : (to_bilin b M).nondegenerate :=
(matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin b).mp h.to_bilin'

@[simp] lemma _root_.matrix.nondegenerate_to_bilin_iff {M : matrix ι ι R₃} (b : basis ι R₃ M₃) :
  (to_bilin b M).nondegenerate ↔ M.nondegenerate :=
by rw [←matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin,
       matrix.nondegenerate_to_bilin'_iff]

-- Lemmas transferring nondegeneracy between a bilinear form and its associated matrix

@[simp] theorem nondegenerate_to_matrix'_iff {B : bilin_form R₃ (ι → R₃)} :
  B.to_matrix'.nondegenerate ↔ B.nondegenerate :=
matrix.nondegenerate_to_bilin'_iff.symm.trans $ (matrix.to_bilin'_to_matrix' B).symm ▸ iff.rfl

theorem nondegenerate.to_matrix' {B : bilin_form R₃ (ι → R₃)} (h : B.nondegenerate) :
  B.to_matrix'.nondegenerate :=
nondegenerate_to_matrix'_iff.mpr h

@[simp] theorem nondegenerate_to_matrix_iff {B : bilin_form R₃ M₃} (b : basis ι R₃ M₃) :
  (to_matrix b B).nondegenerate ↔ B.nondegenerate :=
(matrix.nondegenerate_to_bilin_iff b).symm.trans $ (matrix.to_bilin_to_matrix b B).symm ▸ iff.rfl

theorem nondegenerate.to_matrix {B : bilin_form R₃ M₃} (h : B.nondegenerate)
  (b : basis ι R₃ M₃) : (to_matrix b B).nondegenerate :=
(nondegenerate_to_matrix_iff b).mpr h

-- Some shorthands for combining the above with `matrix.nondegenerate_of_det_ne_zero`

lemma nondegenerate_to_bilin'_iff_det_ne_zero {M : matrix ι ι A} :
  M.to_bilin'.nondegenerate ↔ M.det ≠ 0 :=
by rw [matrix.nondegenerate_to_bilin'_iff, matrix.nondegenerate_iff_det_ne_zero]

theorem nondegenerate_to_bilin'_of_det_ne_zero' (M : matrix ι ι A) (h : M.det ≠ 0) :
  M.to_bilin'.nondegenerate :=
nondegenerate_to_bilin'_iff_det_ne_zero.mpr h

lemma nondegenerate_iff_det_ne_zero {B : bilin_form A M₃}
  (b : basis ι A M₃) : B.nondegenerate ↔ (to_matrix b B).det ≠ 0 :=
by rw [←matrix.nondegenerate_iff_det_ne_zero, nondegenerate_to_matrix_iff]

theorem nondegenerate_of_det_ne_zero (b : basis ι A M₃) (h : (to_matrix b B₃).det ≠ 0) :
  B₃.nondegenerate :=
(nondegenerate_iff_det_ne_zero b).mpr h

end det

end bilin_form
