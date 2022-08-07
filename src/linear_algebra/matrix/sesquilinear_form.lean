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

variables {R R₁ R₂ M₁ M₂ n m o ι : Type*}

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

section comm_ring

variables [comm_ring R] [comm_ring R₁] [comm_ring R₂]
variables [add_comm_monoid M₁] [module R₁ M₁] [add_comm_monoid M₂] [module R₂ M₂]
variables [fintype n] [fintype m]
variables [decidable_eq n] [decidable_eq m]

variables {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def linear_map.to_matrix₂' : ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) ≃ₗ[R] matrix n m R :=
{ inv_fun := matrix.to_linear_map₂'_aux σ₁ σ₂,
  left_inv := linear_map.to_linear_map₂'_aux_to_matrix₂_aux,
  right_inv := matrix.to_matrix₂_aux_to_linear_map₂'_aux,
  ..linear_map.to_matrix₂_aux (λ i, std_basis R₁ (λ _, R₁) i 1) (λ j, std_basis R₂ (λ _, R₂) j 1) }

end comm_ring

end to_matrix'
