/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll
-/

import linear_algebra.matrix.basis
import linear_algebra.matrix.nondegenerate
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_linear_equiv

/-!
# Sesquilinear form

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

variables {R R₁ R₂ M₁ M₂ n m n' m' : Type*}

open_locale big_operators
open finset linear_map matrix
open_locale matrix

section aux_to_linear_map

variables [comm_semiring R] [comm_semiring R₁] [comm_semiring R₂]
variables [fintype n] [fintype m]

variables (σ₁ : R₁ →+* R) (σ₂ : R₂ →+* R)

def matrix.to_linear_map₂'_aux  (f : matrix n m R) :
  (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R :=
mk₂'ₛₗ σ₁ σ₂ (λ (v : n → R₁) (w : m → R₂), ∑ i j, σ₁ (v i) * f i j * σ₂ (w j))
  (λ _ _ _, by simp only [pi.add_apply, map_add, add_mul, sum_add_distrib] )
  (λ _ _ _, by simp only [pi.smul_apply, smul_eq_mul, ring_hom.map_mul, mul_assoc, mul_sum] )
  (λ _ _ _, by simp only [pi.add_apply, map_add, mul_add, sum_add_distrib] )
  (λ _ _ _, by
    simp only [pi.smul_apply, smul_eq_mul, ring_hom.map_mul, mul_assoc, mul_left_comm, mul_sum] )

variables [decidable_eq n] [decidable_eq m]

@[simp] lemma std_basis_apply' (i i' : n) : (std_basis R₁ (λ (_x : n), R₁) i) 1 i' =
  ite (i = i') 1 0  :=
begin
  rw [linear_map.std_basis_apply, function.update_apply, pi.zero_apply],
  congr' 1, rw [eq_iff_iff, eq_comm],
end

@[simp] lemma ring_hom_ite_zero_one (p : Prop) [decidable p] : σ₁ (ite p 0 1) = ite p 0 1 :=
by { split_ifs; simp [h] }

@[simp] lemma ring_hom_ite_one_zero (p : Prop) [decidable p] : σ₁ (ite p 1 0) = ite p 1 0 :=
by { split_ifs; simp [h] }

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

/-! ### `to_matrix'` section

This section deals with the conversion between matrices and sesquilinear forms on `n → R₂`.
-/

variables [comm_ring R] [comm_ring R₁] [comm_ring R₂]
variables [add_comm_monoid M₁] [module R₁ M₁] [add_comm_monoid M₂] [module R₂ M₂]
variables [fintype n] [fintype m]
variables [decidable_eq n] [decidable_eq m]

variables {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear equivalence between sesquilinear forms on `n → R` and `n × n` matrices -/
def linear_map.to_matrixₛₗ₂' : ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) ≃ₗ[R] matrix n m R :=
{ inv_fun := matrix.to_linear_map₂'_aux σ₁ σ₂,
  left_inv := linear_map.to_linear_map₂'_aux_to_matrix₂_aux,
  right_inv := matrix.to_matrix₂_aux_to_linear_map₂'_aux,
  ..linear_map.to_matrix₂_aux (λ i, std_basis R₁ (λ _, R₁) i 1) (λ j, std_basis R₂ (λ _, R₂) j 1) }

def linear_map.to_matrix₂' : ((n → R) →ₗ[R] (m → R) →ₗ[R] R) ≃ₗ[R] matrix n m R :=
linear_map.to_matrixₛₗ₂'

variables (σ₁ σ₂)

/-- The linear equivalence between `n × n` matrices and sesquilinear forms on `n → R` -/
def matrix.to_linear_mapₛₗ₂' : matrix n m R ≃ₗ[R] ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :=
linear_map.to_matrixₛₗ₂'.symm

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def matrix.to_linear_map₂' : matrix n m R ≃ₗ[R] ((n → R) →ₗ[R] (m → R) →ₗ[R] R) :=
linear_map.to_matrixₛₗ₂'.symm

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

@[simp] lemma linear_map.to_matrix₂'_comp (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
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

lemma linear_map.to_matrix₂'_comp_left (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (f : (n' → R) →ₗ[R] (n → R)) : (B.comp f).to_matrix₂' = f.to_matrix'ᵀ ⬝ B.to_matrix₂' :=
by { rw [←linear_map.compl₂_id (B.comp f), ←linear_map.compl₁₂], simp }

lemma linear_map.to_matrix₂'_comp_right (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (f : (m' → R) →ₗ[R] (m → R)) : (B.compl₂ f).to_matrix₂' = B.to_matrix₂' ⬝ f.to_matrix' :=
by { rw [←linear_map.comp_id B, ←linear_map.compl₁₂], simp }

lemma linear_map.mul_to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
  (M : matrix n' n R) (N : matrix m m' R) :
  M ⬝ B.to_matrix₂' ⬝ N = (B.compl₁₂ Mᵀ.to_lin' N.to_lin').to_matrix₂' :=
by simp

lemma linear_map.mul_to_matrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : matrix n' n R) :
  M ⬝ B.to_matrix₂' = (B.comp Mᵀ.to_lin').to_matrix₂' :=
by simp only [B.to_matrix₂'_comp_left, transpose_transpose, to_matrix'_to_lin']

lemma linear_map.to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : matrix m m' R) :
  B.to_matrix₂' ⬝ M = (B.compl₂ M.to_lin').to_matrix₂' :=
by simp only [B.to_matrix₂'_comp_right, to_matrix'_to_lin']

lemma matrix.to_bilin'_comp (M : matrix n m R) (P : matrix n n' R) (Q : matrix m m' R) :
  M.to_linear_map₂'.compl₁₂ P.to_lin' Q.to_lin' = (Pᵀ ⬝ M ⬝ Q).to_linear_map₂' :=
linear_map.to_matrix₂'.injective (by simp)

end to_matrix'
