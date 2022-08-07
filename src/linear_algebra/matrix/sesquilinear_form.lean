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

variables {R R₁ R₂ M N n m o ι : Type*}

section matrix

open_locale big_operators
open finset linear_map matrix
open_locale matrix

variables [fintype ι]

section comm_semiring

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

lemma matrix.to_linear_map₂'_aux_std_basis (f : matrix n m R) (i : n) (j : m) :
  f.to_linear_map₂'_aux σ₁ σ₂ (std_basis R₁ (λ _, R₁) i 1) (std_basis R₂ (λ _, R₂) j 1) = f i j :=
begin
  rw [matrix.to_linear_map₂'_aux, mk₂'ₛₗ_apply],
  have : (∑ i' j', (if i = i' then 1 else 0) * f i' j' * (if j = j' then 1 else 0)) = f i j :=
  begin
    simp_rw [mul_assoc, ←finset.mul_sum],
    simp only [boole_mul, finset.sum_ite_eq, finset.mem_univ, if_true, mul_comm (f _ _)],
  end,
  have h₁ : ∀ i', ite (i = i') 1 0 = σ₁ ((std_basis R₁ (λ (_x : n), R₁) i) 1 i') :=
  begin
    sorry,
  end,
  have h₂ : ∀ j', ite (j = j') 1 0 = σ₂ ((std_basis R₂ (λ (_x : m), R₂) j) 1 j') :=
  begin
    sorry,
  end,
  rw ←this,
  exact finset.sum_congr rfl (λ _ _, finset.sum_congr rfl (λ _ _, by rw [h₁, h₂])),
end

section add_comm_monoid

variables [add_comm_monoid M] [module R M]



end add_comm_monoid

end comm_semiring

end matrix
