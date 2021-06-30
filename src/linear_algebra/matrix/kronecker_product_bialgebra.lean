/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product
Two main definitions:
* Given a commutative semiring α and two α algebras we define kronecker_prod₂, denoted ⊗₂[α], as
  the bilinear Kronecker product
⊗₂[α] : matrix (l n R) →ₗ[α] (matrix m p S) →ₗ[α] (matrix (l × m) (n × p) (R ⊗[α] S).
* In the special case when α=R=S, we compose ⊗₂[α] with the canoical equivalence α ⊗[α] α ≃ α to
  define kronecker_prod, denoted by ⊗ₖ as the α-linear map
  ⊗ₖ  : matrix (l n α) →ₗ[α] (matrix m p α) →ₗ[α] (matrix (l × m) (n × p) (α).

For both products, we prove that it is associative (in theorems `kronecker_prod₂_assoc` and
`prod_assoc`, respectively) as well as the so-called `mixed-product property (in theorems
`kronecker_prod₂_mul` and `prod_mul`, respectively).

I (FAE) wonder if this file should be in `linear_algebra/matrix` or rather in `data/matrix`.
-/

-- For mathlib

universes u v v' u'

-- namespace matrix

-- open matrix

-- variables {α : Type*} [comm_semiring α]
-- variables {γ : Type*} --[add_comm_monoid γ] [module α γ]
-- variables {l m n p l' m' n' p' : Type*}
-- variables [fintype l] [fintype m] [fintype n] [fintype p]
-- variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

-- -- protected
-- -- def linear_equiv_index_assoc [add_comm_monoid γ] [module α γ] :
-- --   matrix ((m × n) × p) ((m' × n') × p') γ ≃ₗ[α] matrix (m × n × p) (m' × n' × p') γ :=
-- -- { to_fun := λ A, reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _) A,
-- --   map_add' := λ _ _, by simp only [reindex_apply, minor_add, pi.add_apply],
-- --   map_smul' := λ _ _, by simp only [reindex_apply, minor_smul, pi.smul_apply],
-- --   inv_fun := λ A, reindex (equiv.prod_assoc _ _ _).symm (equiv.prod_assoc _ _ _).symm A,
-- --   left_inv := λ _, by simp only [equiv.symm_symm, reindex_apply, minor_minor, minor_id_id,
-- --     equiv.symm_comp_self],
-- --   right_inv := λ _, by simp only [equiv.symm_symm, reindex_apply, minor_minor, minor_id_id,
-- --     equiv.self_comp_symm],
-- --   }

-- end matrix

--end mathlib

namespace matrix_bialgebra

open algebra matrix function
open_locale matrix big_operators

variables {α : Type*} [comm_semiring α]
variables {R : Type*} [comm_semiring R]
variables {S : Type*} [comm_semiring S]
variables {β : Type*} [comm_semiring β]
variables [algebra α R] [algebra α S] [algebra α β] [algebra R β] [algebra S β]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def kronecker_biprod (h_Rβ : is_scalar_tower α R β) (h_Sβ : is_scalar_tower α S β) :
  (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) β :=
{ to_fun :=
  begin
    intro A,
    use λ B, λ i j, (algebra_map R β (A i.1 j.1)) * (algebra_map S β (B i.2 j.2)),
    all_goals {intros x y, ext},
    { simp only [pi.add_apply, mul_add, ring_hom.map_add, dmatrix.add_apply] },
    { simp only [pi.smul_apply],
      rw [← is_scalar_tower.algebra_map_smul S x, id.smul_eq_mul, ring_hom.map_mul,
        smul_def, (is_scalar_tower.algebra_map_apply α S β x).symm],
      ring,
      all_goals {exact is_scalar_tower.right} },
  end,
  map_add' := λ _ _, by {simp only [add_mul, ring_hom.map_add, dmatrix.add_apply], refl},
  map_smul' := λ _ _, by {simp_rw [pi.smul_apply, ← smul_def, is_scalar_tower.smul_assoc],
    refl},
  }

variables (h_Rβ : is_scalar_tower α R β) (h_Sβ : is_scalar_tower α S β)

lemma kronecker_biprod_reindex_left (eₗ : l ≃ l') (eₘ : m ≃ m') (A : matrix l m R)
  (B : matrix n p S) : kronecker_biprod h_Rβ h_Sβ (reindex_linear_equiv eₗ eₘ A) B =
  reindex_linear_equiv (eₗ.prod_congr (equiv.refl _)) (eₘ.prod_congr (equiv.refl _))
  (kronecker_biprod h_Rβ h_Sβ A B) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_biprod_reindex_right (eₙ : n ≃ n') (eₚ : p ≃ p') (A : matrix l m R)
  (B : matrix n p S) : kronecker_biprod h_Rβ h_Sβ A (reindex_linear_equiv eₙ eₚ B) =
  reindex_linear_equiv ((equiv.refl _).prod_congr eₙ) ((equiv.refl _).prod_congr eₚ)
  (kronecker_biprod h_Rβ h_Sβ A B) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_biprod_one_one [decidable_eq m] [decidable_eq n] :
  kronecker_biprod h_Rβ h_Sβ (1 : matrix m m R) (1 : matrix n n S) =
    (1 : matrix (m × n) (m × n) β) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, simp [kronecker_biprod, one_apply,
    algebra_map_eq_smul_one, ite_smul, ite_and] }

theorem kronecker_biprod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' S)
  (B' : matrix m' n' S) : kronecker_biprod h_Rβ h_Sβ (A ⬝ B) (A' ⬝ B') =
   (kronecker_biprod h_Rβ h_Sβ A A') ⬝ (kronecker_biprod h_Rβ h_Sβ B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [mul_apply, kronecker_biprod, algebra_map_eq_smul_one, mul_one, algebra.mul_smul_comm,
    linear_map.coe_mk, algebra.smul_mul_assoc, ← finset.univ_product_univ, finset.sum_product],
  simp_rw [finset.sum_smul, finset.smul_sum, ← smul_eq_mul],
  repeat {apply finset.sum_congr, refl, intros _ _,},
  rw [is_scalar_tower.smul_assoc, id.smul_eq_mul (A' i' x_1) (B' x_1 j')],
  simp only [id.smul_eq_mul, ← algebra_map_eq_smul_one, smul_def, ring_hom.map_mul],
  ring_nf,
end

variables (h_ββ : is_scalar_tower α β β)
variables {T : Type*} [comm_semiring T] [algebra α T] [algebra T β] (h_Tβ : is_scalar_tower α T β)
variables (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T)

theorem kronecker_biprod_assoc {T : Type*} [comm_semiring T] [algebra α T] [algebra T β]
  (h_Tβ : is_scalar_tower α T β) (h_ββ : is_scalar_tower α β β) (A : matrix m m' R)
  (B : matrix n n' S) (C : matrix p p' T) :
  @matrix.linear_equiv_index_assoc α _ β m n p m' n' p' _ _ _ _ _ _ _ _
  (kronecker_biprod h_ββ h_Tβ (kronecker_biprod h_Rβ h_Sβ A B) C) =
    kronecker_biprod h_Rβ h_ββ A (kronecker_biprod h_Sβ h_Tβ B C) :=
begin
  simp only [matrix.linear_equiv_index_assoc, kronecker_biprod, linear_map.coe_mk, id.map_eq_self,
    reindex_apply, linear_equiv.coe_mk],
  ext i j,
  simp only [minor_apply, equiv.prod_assoc_symm_apply, mul_assoc],
end

end matrix_bialgebra

namespace kronecker_product

open algebra matrix matrix_bialgebra
open_locale matrix

variables {R : Type*} [comm_semiring R]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def kronecker_prod (hR : is_scalar_tower R R R) (A : matrix l m R) (B : matrix n p R) :
  matrix (l × n) (m × p) R := kronecker_biprod hR hR A B

variable (hR : is_scalar_tower R R R)

localized "infix ` ⊗ₖ  `:100 := kronecker_prod hR _" in kronecker_product
localized "notation x ` ⊗ₖ ` y:100 := kronecker_prod hR x y" in kronecker_product

@[simp] lemma kronecker_prod_ext (A : matrix l m R) (B : matrix n p R) (i : l × n) (j: m × p) :
  (A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2 := rfl

@[simp] lemma kronecker_prod_one_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m R) ⊗ₖ (1 : matrix n n R) = 1 := by {apply kronecker_biprod_one_one}

theorem kronecker_prod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' R)
  (B' : matrix m' n' R) : (A.mul B) ⊗ₖ (A'.mul B') = (A ⊗ₖ A').mul (B ⊗ₖ B') :=
  by {apply kronecker_biprod_mul}

theorem kronecker_prod_assoc (A : matrix m m' R) (B : matrix n n' R) (C : matrix p p' R) :
  matrix.index_assoc (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) := by {apply kronecker_biprod_assoc}

end kronecker_product
