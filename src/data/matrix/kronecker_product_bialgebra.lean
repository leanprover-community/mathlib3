/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import algebra.algebra.tower
import data.matrix.reindex
import data.matrix.kronecker
import linear_algebra.matrix

/-!
# Kronecker biproduct of matrices

Given a commutative semiring α and three α algebras R S β such that β is both a R- and a S-algebra
and there are two instances of scalar towers `is_scalar_tower α R β` and `is_scalar_tower α S β`,
we define `kronecker_biprod` as
the bilinear Kronecker product
kronecker_biprod : matrix (l n R) →ₗ[α] (matrix m p S) →ₗ[α] (matrix (l × m) (n × p) (β).

We prove that it is associative in `kronecker_biprod_assoc`, as well as the so-called
mixed-product property in `kronecker_biprod_mul`.
-/

namespace matrix_bialgebra

open algebra matrix function
open_locale matrix big_operators

section

variables {α R S β : Type*} [comm_semiring α] [comm_semiring R] [comm_semiring S] [comm_semiring β]
variables [algebra α R] [algebra α S] [algebra α β] [algebra R β] [algebra S β]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

-- variables (α β)

-- TODO: move this
-- def algebra.biprod [is_scalar_tower α R β] [is_scalar_tower α S β] :
--   R →ₗ[α] S →ₗ[α] β :=
-- ((algebra.lmul α β).to_linear_map.compl₂ ((algebra.linear_map S β).restrict_scalars α)).comp
--   ((algebra.linear_map R β).restrict_scalars α)

-- @[simp]
-- lemma algebra.biprod_apply [is_scalar_tower α R β] [is_scalar_tower α S β] (r : R) (s : S) :
--   algebra.biprod α β r s = algebra_map R β r * algebra_map S β s := rfl

variables (R S β)

@[simps]
def kronecker_biprod [is_scalar_tower α R β] [is_scalar_tower α S β] :
  (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) β :=
kronecker_map_linear $ is_scalar_tower.algebra.biprod α β

lemma kronecker_biprod_reindex_left (eₗ : l ≃ l') (eₘ : m ≃ m') (A : matrix l m R)
  (B : matrix n p S) [is_scalar_tower α R β] [is_scalar_tower α S β] :
  kronecker_biprod α R S β (reindex_linear_equiv α R eₗ eₘ A) B =
  reindex_linear_equiv α _ (eₗ.prod_congr (equiv.refl _)) (eₘ.prod_congr (equiv.refl _))
  (kronecker_biprod α R S β A B) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_biprod_reindex_right (eₙ : n ≃ n') (eₚ : p ≃ p') (A : matrix l m R)
  (B : matrix n p S) [is_scalar_tower α R β] [is_scalar_tower α S β] :
  kronecker_biprod α R S β A (reindex_linear_equiv α S eₙ eₚ B) =
  reindex_linear_equiv α _ ((equiv.refl _).prod_congr eₙ) ((equiv.refl _).prod_congr eₚ)
  (kronecker_biprod α R S β A B) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_biprod_one_one [decidable_eq m] [decidable_eq n] [is_scalar_tower α R β]
  [is_scalar_tower α S β] : kronecker_biprod α R S β (1 : matrix m m R)
    (1 : matrix n n S) = (1 : matrix (m × n) (m × n) β) :=
kronecker_map_one_one _ (by simp) (by simp) (by simp)

theorem kronecker_biprod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' S)
  (B' : matrix m' n' S) [is_scalar_tower α R β] [is_scalar_tower α S β] :
  kronecker_biprod α R S β (A ⬝ B) (A' ⬝ B') =
    (kronecker_biprod α R S β A A') ⬝ (kronecker_biprod α R S β B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [mul_apply, kronecker_biprod_apply_apply, algebra_map_eq_smul_one, mul_one,
    algebra.mul_smul_comm,
    linear_map.coe_mk, algebra.smul_mul_assoc, ← finset.univ_product_univ, finset.sum_product,
    kronecker_map, algebra.biprod_apply],
  simp_rw [finset.sum_smul, finset.smul_sum, ← smul_eq_mul],
  repeat {apply finset.sum_congr, refl, intros _ _,},
  rw [is_scalar_tower.smul_assoc, id.smul_eq_mul (A' i' x_1) (B' x_1 j')],
  simp only [id.smul_eq_mul, ← algebra_map_eq_smul_one, smul_def, ring_hom.map_mul],
  ring_nf,
end

theorem kronecker_biprod_assoc {T : Type*} [comm_semiring T] [algebra α T] [algebra T β]
 [is_scalar_tower α R β] [is_scalar_tower α S β] [is_scalar_tower α T β] [is_scalar_tower α β β]
 (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  @matrix.linear_equiv_index_assoc m n p _ _ _ m' n' p' _ _ _ β α _ _ _
  (kronecker_biprod α β T β (kronecker_biprod α R S β A B) C) =
    kronecker_biprod α R β β A (kronecker_biprod α S T β B C)
    :=
begin
  simp only [matrix.linear_equiv_index_assoc, kronecker_biprod_apply_apply, linear_map.coe_mk,
    id.map_eq_self,
    reindex_apply, linear_equiv.coe_mk],
  ext i j,
  simp only [equiv.prod_assoc_symm_apply, reindex_linear_equiv_apply, minor_apply, reindex_apply,
    mul_assoc, kronecker_map, algebra.biprod_apply, id.map_eq_self],
end

end matrix_bialgebra

namespace kronecker_product

open algebra matrix matrix_bialgebra
open_locale matrix

variables (R : Type*) [comm_semiring R]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

open_locale kronecker

theorem kronecker_prod_assoc (A : matrix m m' R) (B : matrix n n' R) (C : matrix p p' R) :
  matrix.index_assoc (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) := by {apply kronecker_biprod_assoc}

end kronecker_product
