/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll
-/

import linear_algebra.finsupp_vector_space
import linear_algebra.matrix.basis
import linear_algebra.matrix.nondegenerate
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.sesquilinear_form

/-!
# Sesquilinear form

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the conversion between sesquilinear forms and matrices.

## Main definitions

 * `matrix.to_linear_map₂` given a basis define a bilinear form
 * `matrix.to_linear_map₂'` define the bilinear form on `n → R`
 * `linear_map.to_matrix₂`: calculate the matrix coefficients of a bilinear form
 * `linear_map.to_matrix₂'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Todos

At the moment this is quite a literal port from `matrix.bilinear_form`. Everything should be
generalized to fully semibilinear forms.

## Tags

sesquilinear_form, matrix, basis

-/

variables {R R₁ R₂ M M₁ M₂ M₁' M₂' n m n' m' ι : Type*}

open_locale big_operators
open finset linear_map matrix
open_locale matrix

section aux_to_linear_map

variables [comm_semiring R] [comm_semiring R₁] [comm_semiring R₂]
variables [fintype n] [fintype m]

variables (σ₁ : R₁ →+* R) (σ₂ : R₂ →+* R)


/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_linear_map₂'`. -/
def matrix.to_linear_map₂'_aux  (f : matrix n m R) :
  (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R :=
mk₂'ₛₗ σ₁ σ₂ (λ (v : n → R₁) (w : m → R₂), ∑ i j, σ₁ (v i) * f i j * σ₂ (w j))
  (λ _ _ _, by simp only [pi.add_apply, map_add, add_mul, sum_add_distrib] )
  (λ _ _ _, by simp only [pi.smul_apply, smul_eq_mul, ring_hom.map_mul, mul_assoc, mul_sum] )
  (λ _ _ _, by simp only [pi.add_apply, map_add, mul_add, sum_add_distrib] )
  (λ _ _ _, by
    simp only [pi.smul_apply, smul_eq_mul, ring_hom.map_mul, mul_assoc, mul_left_comm, mul_sum] )

variables [decidable_eq n] [decidable_eq m]

lemma matrix.to_linear_map₂'_aux_std_basis (f : matrix n m R) (i : n) (j : m) :
  f.to_linear_map₂'_aux σ₁ σ₂ (std_basis R₁ (λ _, R₁) i 1) (std_basis R₂ (λ _, R₂) j 1) = f i j :=
begin
  rw [matrix.to_linear_map₂'_aux, mk₂'ₛₗ_apply],
  have : (∑ i' j', (if i = i' then 1 else 0) * f i' j' * (if j = j' then 1 else 0)) = f i j :=
  begin
    simp_rw [mul_assoc, ←finset.mul_sum],
    simp only [boole_mul, finset.sum_ite_eq, finset.mem_univ, if_true, mul_comm (f _ _)],
  end,
  rw ←this,
  exact finset.sum_congr rfl (λ _ _, finset.sum_congr rfl (λ _ _, by simp)),
end

end aux_to_linear_map

section aux_to_matrix

section comm_semiring

variables [comm_semiring R] [comm_semiring R₁] [comm_semiring R₂]
variables [add_comm_monoid M₁] [module R₁ M₁] [add_comm_monoid M₂] [module R₂ M₂]

variables {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear map from sesquilinear forms to `matrix n m R` given an `n`-indexed basis for `M₁`
and an `m`-indexed basis for `M₂`.

This is an auxiliary definition for the equivalence `matrix.to_linear_mapₛₗ₂'`. -/
def linear_map.to_matrix₂_aux (b₁ : n → M₁) (b₂ : m → M₂) :
  (M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R) →ₗ[R] matrix n m R :=
{ to_fun := λ f, of $ λ i j, f (b₁ i) (b₂ j),
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl }

@[simp] lemma linear_map.to_matrix₂_aux_apply (f : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R)
  (b₁ : n → M₁) (b₂ : m → M₂) (i : n) (j : m) :
  linear_map.to_matrix₂_aux b₁ b₂ f i j = f (b₁ i) (b₂ j) := rfl

end comm_semiring

section comm_ring

variables [comm_ring R] [comm_ring R₁] [comm_ring R₂]
variables [add_comm_monoid M₁] [module R₁ M₁] [add_comm_monoid M₂] [module R₂ M₂]
variables [fintype n] [fintype m]
variables [decidable_eq n] [decidable_eq m]

variables {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

lemma linear_map.to_linear_map₂'_aux_to_matrix₂_aux (f : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :
  matrix.to_linear_map₂'_aux σ₁ σ₂ (linear_map.to_matrix₂_aux
    (λ i, std_basis R₁ (λ _, R₁) i 1) (λ j, std_basis R₂ (λ _, R₂) j 1) f) = f :=
begin
  refine ext_basis (pi.basis_fun R₁ n) (pi.basis_fun R₂ m) (λ i j, _),
  simp_rw [pi.basis_fun_apply, matrix.to_linear_map₂'_aux_std_basis,
    linear_map.to_matrix₂_aux_apply],
end

lemma matrix.to_matrix₂_aux_to_linear_map₂'_aux (f : matrix n m R) :
  linear_map.to_matrix₂_aux (λ i, std_basis R₁ (λ _, R₁) i 1) (λ j, std_basis R₂ (λ _, R₂) j 1)
    (f.to_linear_map₂'_aux σ₁ σ₂) = f :=
by { ext i j, simp_rw [linear_map.to_matrix₂_aux_apply, matrix.to_linear_map₂'_aux_std_basis] }

end comm_ring

end aux_to_matrix

section to_matrix'

/-! ### Bilinear forms over `n → R`

This section deals with the conversion between matrices and sesquilinear forms on `n → R`.
-/

variables [comm_ring R] [comm_ring R₁] [comm_ring R₂]
variables [fintype n] [fintype m]
variables [decidable_eq n] [decidable_eq m]

variables {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear equivalence between sesquilinear forms and `n × m` matrices -/
def linear_map.to_matrixₛₗ₂' : ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) ≃ₗ[R] matrix n m R :=
{ to_fun := linear_map.to_matrix₂_aux _ _,
  inv_fun := matrix.to_linear_map₂'_aux σ₁ σ₂,
  left_inv := linear_map.to_linear_map₂'_aux_to_matrix₂_aux,
  right_inv := matrix.to_matrix₂_aux_to_linear_map₂'_aux,
  ..linear_map.to_matrix₂_aux (λ i, std_basis R₁ (λ _, R₁) i 1) (λ j, std_basis R₂ (λ _, R₂) j 1) }

/-- The linear equivalence between bilinear forms and `n × m` matrices -/
def linear_map.to_matrix₂' : ((n → R) →ₗ[R] (m → R) →ₗ[R] R) ≃ₗ[R] matrix n m R :=
linear_map.to_matrixₛₗ₂'

variables (σ₁ σ₂)

/-- The linear equivalence between `n × n` matrices and sesquilinear forms on `n → R` -/
def matrix.to_linear_mapₛₗ₂' : matrix n m R ≃ₗ[R] ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :=
linear_map.to_matrixₛₗ₂'.symm

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def matrix.to_linear_map₂' : matrix n m R ≃ₗ[R] ((n → R) →ₗ[R] (m → R) →ₗ[R] R) :=
linear_map.to_matrix₂'.symm

lemma matrix.to_linear_mapₛₗ₂'_aux_eq (M : matrix n m R) :
  matrix.to_linear_map₂'_aux σ₁ σ₂ M = matrix.to_linear_mapₛₗ₂' σ₁ σ₂ M := rfl

lemma matrix.to_linear_mapₛₗ₂'_apply (M : matrix n m R) (x : n → R₁) (y : m → R₂) :
  matrix.to_linear_mapₛₗ₂' σ₁ σ₂ M x y = ∑ i j, σ₁ (x i) * M i j * σ₂ (y j) := rfl

lemma matrix.to_linear_map₂'_apply (M : matrix n m R) (x : n → R) (y : m → R) :
  matrix.to_linear_map₂' M x y = ∑ i j, x i * M i j * y j := rfl

lemma matrix.to_linear_map₂'_apply' (M : matrix n m R) (v : n → R) (w : m → R) :
  matrix.to_linear_map₂' M v w = matrix.dot_product v (M.mul_vec w) :=
begin
  simp_rw [matrix.to_linear_map₂'_apply, matrix.dot_product,
           matrix.mul_vec, matrix.dot_product],
  refine finset.sum_congr rfl (λ _ _, _),
  rw finset.mul_sum,
  refine finset.sum_congr rfl (λ _ _, _),
  rw ← mul_assoc,
end

@[simp] lemma matrix.to_linear_mapₛₗ₂'_std_basis (M : matrix n m R) (i : n) (j : m) :
  matrix.to_linear_mapₛₗ₂' σ₁ σ₂ M (std_basis R₁ (λ _, R₁) i 1) (std_basis R₂ (λ _, R₂) j 1) =
    M i j :=
matrix.to_linear_map₂'_aux_std_basis σ₁ σ₂ M i j

@[simp] lemma matrix.to_linear_map₂'_std_basis (M : matrix n m R) (i : n) (j : m) :
  matrix.to_linear_map₂' M (std_basis R (λ _, R) i 1) (std_basis R (λ _, R) j 1) =
    M i j :=
matrix.to_linear_map₂'_aux_std_basis _ _ M i j

@[simp] lemma linear_map.to_matrixₛₗ₂'_symm :
  (linear_map.to_matrixₛₗ₂'.symm : matrix n m R ≃ₗ[R] _) = matrix.to_linear_mapₛₗ₂' σ₁ σ₂ :=
rfl

@[simp] lemma matrix.to_linear_mapₛₗ₂'_symm :
  ((matrix.to_linear_mapₛₗ₂' σ₁ σ₂).symm : _ ≃ₗ[R] matrix n m R) = linear_map.to_matrixₛₗ₂' :=
linear_map.to_matrixₛₗ₂'.symm_symm

@[simp] lemma matrix.to_linear_mapₛₗ₂'_to_matrix' (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :
  matrix.to_linear_mapₛₗ₂' σ₁ σ₂ (linear_map.to_matrixₛₗ₂' B) = B :=
(matrix.to_linear_mapₛₗ₂' σ₁ σ₂).apply_symm_apply B

@[simp] lemma matrix.to_linear_map₂'_to_matrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) :
  matrix.to_linear_map₂' (linear_map.to_matrix₂' B) = B :=
matrix.to_linear_map₂'.apply_symm_apply B

@[simp] lemma linear_map.to_matrix'_to_linear_mapₛₗ₂' (M : matrix n m R) :
  linear_map.to_matrixₛₗ₂' (matrix.to_linear_mapₛₗ₂' σ₁ σ₂ M) = M :=
linear_map.to_matrixₛₗ₂'.apply_symm_apply M

@[simp] lemma linear_map.to_matrix'_to_linear_map₂' (M : matrix n m R) :
  linear_map.to_matrix₂' (matrix.to_linear_map₂' M) = M :=
linear_map.to_matrixₛₗ₂'.apply_symm_apply M

@[simp] lemma linear_map.to_matrixₛₗ₂'_apply (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) (i : n)
  (j : m): linear_map.to_matrixₛₗ₂' B i j =
    B (std_basis R₁ (λ _, R₁) i 1) (std_basis R₂ (λ _, R₂) j 1) :=
rfl

@[simp] lemma linear_map.to_matrix₂'_apply (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (i : n) (j : m):
  linear_map.to_matrix₂' B i j =
    B (std_basis R (λ _, R) i 1) (std_basis R (λ _, R) j 1) :=
rfl

variables [fintype n'] [fintype m']
variables [decidable_eq n'] [decidable_eq m']

@[simp] lemma linear_map.to_matrix₂'_compl₁₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (l : (n' → R) →ₗ[R] (n → R)) (r : (m' → R) →ₗ[R] (m → R)) :
  (B.compl₁₂ l r).to_matrix₂' = l.to_matrix'ᵀ ⬝ B.to_matrix₂' ⬝ r.to_matrix' :=
begin
  ext i j,
  simp only [linear_map.to_matrix₂'_apply, linear_map.compl₁₂_apply, transpose_apply,
    matrix.mul_apply, linear_map.to_matrix', linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ←linear_map.sum_repr_mul_repr_mul (pi.basis_fun R n) (pi.basis_fun R m)
    (l _) (r _) },
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

lemma linear_map.to_matrix₂'_comp (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (f : (n' → R) →ₗ[R] (n → R)) : (B.comp f).to_matrix₂' = f.to_matrix'ᵀ ⬝ B.to_matrix₂' :=
by { rw [←linear_map.compl₂_id (B.comp f), ←linear_map.compl₁₂], simp }

lemma linear_map.to_matrix₂'_compl₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (f : (m' → R) →ₗ[R] (m → R)) : (B.compl₂ f).to_matrix₂' = B.to_matrix₂' ⬝ f.to_matrix' :=
by { rw [←linear_map.comp_id B, ←linear_map.compl₁₂], simp }

lemma linear_map.mul_to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (M : matrix n' n R) (N : matrix m m' R) :
  M ⬝ B.to_matrix₂' ⬝ N = (B.compl₁₂ Mᵀ.to_lin' N.to_lin').to_matrix₂' :=
by simp

lemma linear_map.mul_to_matrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : matrix n' n R) :
  M ⬝ B.to_matrix₂' = (B.comp Mᵀ.to_lin').to_matrix₂' :=
by simp only [B.to_matrix₂'_comp, transpose_transpose, to_matrix'_to_lin']

lemma linear_map.to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : matrix m m' R) :
  B.to_matrix₂' ⬝ M = (B.compl₂ M.to_lin').to_matrix₂' :=
by simp only [B.to_matrix₂'_compl₂, to_matrix'_to_lin']

lemma matrix.to_linear_map₂'_comp (M : matrix n m R) (P : matrix n n' R) (Q : matrix m m' R) :
  M.to_linear_map₂'.compl₁₂ P.to_lin' Q.to_lin' = (Pᵀ ⬝ M ⬝ Q).to_linear_map₂' :=
linear_map.to_matrix₂'.injective (by simp)

end to_matrix'

section to_matrix

/-! ### Bilinear forms over arbitrary vector spaces

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/

variables [comm_ring R]
variables [add_comm_monoid M₁] [module R M₁] [add_comm_monoid M₂] [module R M₂]

variables [decidable_eq n] [fintype n]
variables [decidable_eq m] [fintype m]
variables (b₁ : basis n R M₁) (b₂ : basis m R M₂)

/-- `linear_map.to_matrix₂ b₁ b₂` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def linear_map.to_matrix₂ : (M₁ →ₗ[R] M₂ →ₗ[R] R) ≃ₗ[R] matrix n m R :=
(b₁.equiv_fun.arrow_congr (b₂.equiv_fun.arrow_congr (linear_equiv.refl R R))).trans
  linear_map.to_matrix₂'

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def matrix.to_linear_map₂ : matrix n m R ≃ₗ[R] (M₁ →ₗ[R] M₂ →ₗ[R] R) :=
(linear_map.to_matrix₂ b₁ b₂).symm

-- We make this and not `linear_map.to_matrix₂` a `simp` lemma to avoid timeouts
@[simp] lemma linear_map.to_matrix₂_apply (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (i : n) (j : m) :
  linear_map.to_matrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j) :=
by simp only [linear_map.to_matrix₂, linear_equiv.trans_apply, linear_map.to_matrix₂'_apply,
  linear_equiv.trans_apply, linear_map.to_matrix₂'_apply, linear_equiv.arrow_congr_apply,
  basis.equiv_fun_symm_std_basis, linear_equiv.refl_apply]

@[simp] lemma matrix.to_linear_map₂_apply (M : matrix n m R) (x : M₁) (y : M₂) :
  matrix.to_linear_map₂ b₁ b₂ M x y = ∑ i j, b₁.repr x i * M i j * b₂.repr y j :=
rfl

-- Not a `simp` lemma since `linear_map.to_matrix₂` needs an extra argument
lemma linear_map.to_matrix₂_aux_eq (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
  linear_map.to_matrix₂_aux b₁ b₂ B = linear_map.to_matrix₂ b₁ b₂ B :=
ext (λ i j, by rw [linear_map.to_matrix₂_apply, linear_map.to_matrix₂_aux_apply])

@[simp] lemma linear_map.to_matrix₂_symm :
  (linear_map.to_matrix₂ b₁ b₂).symm = matrix.to_linear_map₂ b₁ b₂ :=
rfl

@[simp] lemma matrix.to_linear_map₂_symm :
  (matrix.to_linear_map₂ b₁ b₂).symm = linear_map.to_matrix₂ b₁ b₂ :=
(linear_map.to_matrix₂ b₁ b₂).symm_symm

lemma matrix.to_linear_map₂_basis_fun :
  matrix.to_linear_map₂ (pi.basis_fun R n) (pi.basis_fun R m) = matrix.to_linear_map₂' :=
by { ext M, simp only [matrix.to_linear_map₂_apply, matrix.to_linear_map₂'_apply, pi.basis_fun_repr,
  coe_comp, function.comp_app]}

lemma linear_map.to_matrix₂_basis_fun :
  linear_map.to_matrix₂ (pi.basis_fun R n) (pi.basis_fun R m) = linear_map.to_matrix₂' :=
by { ext B, rw [linear_map.to_matrix₂_apply, linear_map.to_matrix₂'_apply,
                pi.basis_fun_apply, pi.basis_fun_apply] }

@[simp] lemma matrix.to_linear_map₂_to_matrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
  matrix.to_linear_map₂ b₁ b₂ (linear_map.to_matrix₂ b₁ b₂ B) = B :=
(matrix.to_linear_map₂ b₁ b₂).apply_symm_apply B

@[simp] lemma linear_map.to_matrix₂_to_linear_map₂ (M : matrix n m R) :
  linear_map.to_matrix₂ b₁ b₂ (matrix.to_linear_map₂ b₁ b₂ M) = M :=
(linear_map.to_matrix₂ b₁ b₂).apply_symm_apply M

variables [add_comm_monoid M₁'] [module R M₁']
variables [add_comm_monoid M₂'] [module R M₂']
variables (b₁' : basis n' R M₁')
variables (b₂' : basis m' R M₂')
variables [fintype n'] [fintype m']
variables [decidable_eq n'] [decidable_eq m']

-- Cannot be a `simp` lemma because `b₁` and `b₂` must be inferred.
lemma linear_map.to_matrix₂_compl₁₂
  (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (l : M₁' →ₗ[R] M₁) (r : M₂' →ₗ[R] M₂) :
  linear_map.to_matrix₂ b₁' b₂' (B.compl₁₂ l r) =
    (to_matrix b₁' b₁ l)ᵀ ⬝ linear_map.to_matrix₂ b₁ b₂ B ⬝ to_matrix b₂' b₂ r :=
begin
  ext i j,
  simp only [linear_map.to_matrix₂_apply, compl₁₂_apply, transpose_apply, matrix.mul_apply,
    linear_map.to_matrix_apply, linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ←linear_map.sum_repr_mul_repr_mul b₁ b₂ },
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

lemma linear_map.to_matrix₂_comp (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₁' →ₗ[R] M₁) :
  linear_map.to_matrix₂ b₁' b₂ (B.comp f) = (to_matrix b₁' b₁ f)ᵀ ⬝ linear_map.to_matrix₂ b₁ b₂ B :=
begin
  rw [←linear_map.compl₂_id (B.comp f), ←linear_map.compl₁₂, linear_map.to_matrix₂_compl₁₂ b₁ b₂],
  simp,
end

lemma linear_map.to_matrix₂_compl₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₂' →ₗ[R] M₂) :
  linear_map.to_matrix₂ b₁ b₂' (B.compl₂ f) =
  linear_map.to_matrix₂ b₁ b₂ B ⬝ (to_matrix b₂' b₂ f) :=
by { rw [←linear_map.comp_id B, ←linear_map.compl₁₂, linear_map.to_matrix₂_compl₁₂ b₁ b₂], simp }

@[simp]
lemma linear_map.to_matrix₂_mul_basis_to_matrix (c₁ : basis n' R M₁) (c₂ : basis m' R M₂)
  (B : M₁ →ₗ[R] M₂ →ₗ[R] R) : (b₁.to_matrix c₁)ᵀ ⬝ linear_map.to_matrix₂ b₁ b₂ B ⬝ b₂.to_matrix c₂ =
  linear_map.to_matrix₂ c₁ c₂ B :=
begin
  simp_rw ←linear_map.to_matrix_id_eq_basis_to_matrix,
  rw [←linear_map.to_matrix₂_compl₁₂, linear_map.compl₁₂_id_id],
end

lemma linear_map.mul_to_matrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R)
  (M : matrix n' n R) (N : matrix m m' R) :
  M ⬝ linear_map.to_matrix₂ b₁ b₂ B ⬝ N =
    linear_map.to_matrix₂ b₁' b₂' (B.compl₁₂ (to_lin b₁' b₁ Mᵀ) (to_lin b₂' b₂ N)) :=
by simp_rw [linear_map.to_matrix₂_compl₁₂ b₁ b₂, to_matrix_to_lin, transpose_transpose]

lemma linear_map.mul_to_matrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : matrix n' n R) :
  M ⬝ linear_map.to_matrix₂ b₁ b₂ B =
    linear_map.to_matrix₂ b₁' b₂ (B.comp (to_lin b₁' b₁ Mᵀ)) :=
by rw [linear_map.to_matrix₂_comp b₁, to_matrix_to_lin, transpose_transpose]

lemma linear_map.to_matrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : matrix m m' R) :
  linear_map.to_matrix₂ b₁ b₂ B ⬝ M =
    linear_map.to_matrix₂ b₁ b₂' (B.compl₂ (to_lin b₂' b₂ M)) :=
by rw [linear_map.to_matrix₂_compl₂ b₁, to_matrix_to_lin]

lemma matrix.to_linear_map₂_compl₁₂ (M : matrix n m R) (P : matrix n n' R) (Q : matrix m m' R) :
  (matrix.to_linear_map₂ b₁ b₂ M).compl₁₂ (to_lin b₁' b₁ P) (to_lin b₂' b₂ Q) =
  matrix.to_linear_map₂ b₁' b₂' (Pᵀ ⬝ M ⬝ Q) :=
(linear_map.to_matrix₂ b₁' b₂').injective
  (by simp only [linear_map.to_matrix₂_compl₁₂ b₁ b₂, linear_map.to_matrix₂_to_linear_map₂,
    to_matrix_to_lin])

end to_matrix

/-! ### Adjoint pairs-/

section matrix_adjoints
open_locale matrix

variables [comm_ring R]
variables [add_comm_monoid M₁] [module R M₁] [add_comm_monoid M₂] [module R M₂]
variables [fintype n] [fintype n']

variables (b₁ : basis n R M₁) (b₂ : basis n' R M₂)
variables (J J₂ : matrix n n R) (J' : matrix n' n' R)
variables (A : matrix n' n R) (A' : matrix n n' R)
variables (A₁ : matrix n n R)

/-- The condition for the matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₃`. -/
def matrix.is_adjoint_pair := Aᵀ ⬝ J' = J ⬝ A'

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def matrix.is_self_adjoint := matrix.is_adjoint_pair J J A₁ A₁

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def matrix.is_skew_adjoint := matrix.is_adjoint_pair J J A₁ (-A₁)

variables [decidable_eq n] [decidable_eq n']

@[simp] lemma is_adjoint_pair_to_linear_map₂' :
  is_adjoint_pair (matrix.to_linear_map₂' J) (matrix.to_linear_map₂' J')
      (matrix.to_lin' A) (matrix.to_lin' A') ↔
    matrix.is_adjoint_pair J J' A A' :=
begin
  rw is_adjoint_pair_iff_comp_eq_compl₂,
  have h : ∀ (B B' : (n → R) →ₗ[R] (n' → R) →ₗ[R] R), B = B' ↔
    (linear_map.to_matrix₂' B) = (linear_map.to_matrix₂' B') :=
  begin
    intros B B',
    split; intros h,
    { rw h },
    { exact linear_map.to_matrix₂'.injective h },
  end,
  simp_rw [h, linear_map.to_matrix₂'_comp, linear_map.to_matrix₂'_compl₂,
    linear_map.to_matrix'_to_lin', linear_map.to_matrix'_to_linear_map₂'],
  refl,
end

@[simp] lemma is_adjoint_pair_to_linear_map₂ :
  is_adjoint_pair (matrix.to_linear_map₂ b₁ b₁ J) (matrix.to_linear_map₂ b₂ b₂ J')
      (matrix.to_lin b₁ b₂ A) (matrix.to_lin b₂ b₁ A') ↔
    matrix.is_adjoint_pair J J' A A' :=
begin
  rw is_adjoint_pair_iff_comp_eq_compl₂,
  have h : ∀ (B B' : M₁ →ₗ[R] M₂ →ₗ[R] R), B = B' ↔
    (linear_map.to_matrix₂ b₁ b₂ B) = (linear_map.to_matrix₂ b₁ b₂ B') :=
  begin
    intros B B',
    split; intros h,
    { rw h },
    { exact (linear_map.to_matrix₂ b₁ b₂).injective h },
  end,
  simp_rw [h, linear_map.to_matrix₂_comp b₂ b₂, linear_map.to_matrix₂_compl₂ b₁ b₁,
    linear_map.to_matrix_to_lin, linear_map.to_matrix₂_to_linear_map₂],
  refl,
end

lemma matrix.is_adjoint_pair_equiv (P : matrix n n R) (h : is_unit P) :
  (Pᵀ ⬝ J ⬝ P).is_adjoint_pair (Pᵀ ⬝ J ⬝ P) A₁ A₁ ↔
    J.is_adjoint_pair J (P ⬝ A₁ ⬝ P⁻¹) (P ⬝ A₁ ⬝ P⁻¹) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
begin
  let u := P.nonsing_inv_unit h',
  let v := Pᵀ.nonsing_inv_unit (P.is_unit_det_transpose h'),
  let x := A₁ᵀ * Pᵀ * J,
  let y := J * P * A₁,
  suffices : x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹,
  { dunfold matrix.is_adjoint_pair,
    repeat { rw matrix.transpose_mul, },
    simp only [←matrix.mul_eq_mul, ←mul_assoc, P.transpose_nonsing_inv],
    conv_lhs { to_rhs, rw [mul_assoc, mul_assoc], congr, skip, rw ←mul_assoc, },
    conv_rhs { rw [mul_assoc, mul_assoc], conv { to_lhs, congr, skip, rw ←mul_assoc }, },
    exact this, },
  rw units.eq_mul_inv_iff_mul_eq, conv_rhs { rw mul_assoc, }, rw v.inv_mul_eq_iff_eq_mul,
end

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule : submodule R (matrix n n R) :=
(is_pair_self_adjoint_submodule (matrix.to_linear_map₂' J) (matrix.to_linear_map₂' J₂)).map
  ((linear_map.to_matrix' : ((n → R) →ₗ[R] (n → R)) ≃ₗ[R] matrix n n R) :
  ((n → R) →ₗ[R] (n → R)) →ₗ[R] matrix n n R)

@[simp] lemma mem_pair_self_adjoint_matrices_submodule :
  A₁ ∈ (pair_self_adjoint_matrices_submodule J J₂) ↔ matrix.is_adjoint_pair J J₂ A₁ A₁ :=
begin
  simp only [pair_self_adjoint_matrices_submodule, linear_equiv.coe_coe,
    linear_map.to_matrix'_apply, submodule.mem_map, mem_is_pair_self_adjoint_submodule],
  split,
  { rintros ⟨f, hf, hA⟩,
    have hf' : f = A₁.to_lin' := by rw [←hA, matrix.to_lin'_to_matrix'], rw hf' at hf,
    rw ← is_adjoint_pair_to_linear_map₂',
    exact hf, },
  { intros h, refine ⟨A₁.to_lin', _, linear_map.to_matrix'_to_lin' _⟩,
    exact (is_adjoint_pair_to_linear_map₂' _ _ _ _).mpr h, },
end

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule : submodule R (matrix n n R) :=
  pair_self_adjoint_matrices_submodule J J

@[simp] lemma mem_self_adjoint_matrices_submodule :
  A₁ ∈ self_adjoint_matrices_submodule J ↔ J.is_self_adjoint A₁ :=
by { erw mem_pair_self_adjoint_matrices_submodule, refl, }

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule : submodule R (matrix n n R) :=
  pair_self_adjoint_matrices_submodule (-J) J

@[simp] lemma mem_skew_adjoint_matrices_submodule :
  A₁ ∈ skew_adjoint_matrices_submodule J ↔ J.is_skew_adjoint A₁ :=
begin
  erw mem_pair_self_adjoint_matrices_submodule,
  simp [matrix.is_skew_adjoint, matrix.is_adjoint_pair],
end

end matrix_adjoints

namespace linear_map

/-! ### Nondegenerate bilinear forms-/

section det

open matrix

variables [comm_ring R₁] [add_comm_monoid M₁] [module R₁ M₁]
variables [decidable_eq ι] [fintype ι]

lemma _root_.matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂
  {M : matrix ι ι R₁} (b : basis ι R₁ M₁) : M.to_linear_map₂'.separating_left ↔
  (matrix.to_linear_map₂ b b M).separating_left :=
(separating_left_congr_iff b.equiv_fun.symm b.equiv_fun.symm).symm

variables (B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁)

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form

theorem _root_.matrix.nondegenerate.to_linear_map₂' {M : matrix ι ι R₁} (h : M.nondegenerate) :
  M.to_linear_map₂'.separating_left :=
λ x hx, h.eq_zero_of_ortho $ λ y, by simpa only [to_linear_map₂'_apply'] using hx y

@[simp] lemma _root_.matrix.separating_left_to_linear_map₂'_iff {M : matrix ι ι R₁} :
  M.to_linear_map₂'.separating_left ↔ M.nondegenerate :=
⟨λ h v hv, h v $ λ w, (M.to_linear_map₂'_apply' _ _).trans $ hv w,
  matrix.nondegenerate.to_linear_map₂'⟩

theorem _root_.matrix.nondegenerate.to_linear_map₂ {M : matrix ι ι R₁} (h : M.nondegenerate)
  (b : basis ι R₁ M₁) : (to_linear_map₂ b b M).separating_left :=
(matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂ b).mp h.to_linear_map₂'

@[simp] lemma _root_.matrix.separating_left_to_linear_map₂_iff {M : matrix ι ι R₁}
  (b : basis ι R₁ M₁) : (to_linear_map₂ b b M).separating_left ↔ M.nondegenerate :=
by rw [←matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂,
       matrix.separating_left_to_linear_map₂'_iff]

-- Lemmas transferring nondegeneracy between a bilinear form and its associated matrix

@[simp] theorem nondegenerate_to_matrix₂'_iff {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁} :
  B.to_matrix₂'.nondegenerate ↔ B.separating_left :=
matrix.separating_left_to_linear_map₂'_iff.symm.trans $
  (matrix.to_linear_map₂'_to_matrix' B).symm ▸ iff.rfl

theorem separating_left.to_matrix₂' {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁}
  (h : B.separating_left) : B.to_matrix₂'.nondegenerate :=
nondegenerate_to_matrix₂'_iff.mpr h

@[simp] theorem nondegenerate_to_matrix_iff {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁}
  (b : basis ι R₁ M₁) : (to_matrix₂ b b B).nondegenerate ↔ B.separating_left :=
(matrix.separating_left_to_linear_map₂_iff b).symm.trans $
  (matrix.to_linear_map₂_to_matrix₂ b b B).symm ▸ iff.rfl

theorem separating_left.to_matrix₂ {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (h : B.separating_left)
  (b : basis ι R₁ M₁) : (to_matrix₂ b b B).nondegenerate :=
(nondegenerate_to_matrix_iff b).mpr h

-- Some shorthands for combining the above with `matrix.nondegenerate_of_det_ne_zero`

variables [is_domain R₁]

lemma separating_left_to_linear_map₂'_iff_det_ne_zero {M : matrix ι ι R₁} :
  M.to_linear_map₂'.separating_left ↔ M.det ≠ 0 :=
by rw [matrix.separating_left_to_linear_map₂'_iff, matrix.nondegenerate_iff_det_ne_zero]

theorem separating_left_to_linear_map₂'_of_det_ne_zero' (M : matrix ι ι R₁) (h : M.det ≠ 0) :
  M.to_linear_map₂'.separating_left :=
separating_left_to_linear_map₂'_iff_det_ne_zero.mpr h

lemma separating_left_iff_det_ne_zero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁}
  (b : basis ι R₁ M₁) : B.separating_left ↔ (to_matrix₂ b b B).det ≠ 0 :=
by rw [←matrix.nondegenerate_iff_det_ne_zero, nondegenerate_to_matrix_iff]

theorem separating_left_of_det_ne_zero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : basis ι R₁ M₁)
  (h : (to_matrix₂ b b B).det ≠ 0) :
  B.separating_left :=
(separating_left_iff_det_ne_zero b).mpr h

end det

end linear_map
