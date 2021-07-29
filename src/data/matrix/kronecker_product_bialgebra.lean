/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import data.matrix.reindex
import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product
Two main definitions:
* Given a commutative semiring α and three α algebras R S β such that β is both a R- and a S-algebra
  and there are two instances of scalar towers `is_scalar_tower α R β` and `is_scalar_tower α S β`,
  we define `kronecker_biprod` as
  the bilinear Kronecker product
  kronecker_biprod : matrix (l n R) →ₗ[α] (matrix m p S) →ₗ[α] (matrix (l × m) (n × p) (β).
* In the special case when R=α=S=β, we define kronecker_prod, denoted by ⊗ₖ as the R-linear map
  ⊗ₖ  : matrix (l n R) →ₗ[R] (matrix m p R) →ₗ[R] (matrix (l × m) (n × p) R).

For both products, we prove that it is associative (in theorems `kronecker_biprod_assoc` and
`kronecker_prod_assoc`, respectively) as well as the so-called `mixed-product property (in theorems
`kronecker_biprod_mul` and `kronecker_prod_mul`, respectively).
-/

namespace matrix_bialgebra

open algebra matrix function
open_locale matrix big_operators

section

variables {R α β γ : Type*} {l m n p : Type*} [fintype l] [fintype m] [fintype n] [fintype p]

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B` -/
@[simp] def kronecker_map (f : α → β → γ) (A : matrix l m α) (B : matrix n p β) :
  matrix (l × n) (m × p) γ
| i j := f (A i.1 j.1) (B i.2 j.2)

lemma kronecker_map_zero_left [has_zero α] [has_zero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0)
  (B : matrix n p β) :
  kronecker_map f (0 : matrix l m α) B = 0:=
ext $ λ i j,hf _

lemma kronecker_map_zero_right [has_zero β] [has_zero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0)
  (A : matrix l m α) :
  kronecker_map f A (0 : matrix n p β) = 0 :=
ext $ λ i j, hf _

lemma kronecker_map_add_left [has_add α] [has_add γ] (f : α → β → γ)
  (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b)
  (A₁ A₂ : matrix l m α) (B : matrix n p β) :
  kronecker_map f (A₁ + A₂) B = kronecker_map f A₁ B + kronecker_map f A₂ B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_add_right [has_add β] [has_add γ] (f : α → β → γ)
  (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂)
  (A : matrix l m α) (B₁ B₂ : matrix n p β) :
  kronecker_map f A (B₁ + B₂) = kronecker_map f A B₁ + kronecker_map f A B₂ :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_smul_left [has_scalar R α] [has_scalar R γ] (f : α → β → γ)
  (hf : ∀ (r : R) a b, f (r • a) b = r • f a b) (r : R)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (r • A) B = r • kronecker_map f A B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_smul_right [has_scalar R β] [has_scalar R γ] (f : α → β → γ)
  (hf : ∀ (r : R) a b, f a (r • b) = r • f a b) (r : R)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (r • B) = r • kronecker_map f A B :=
ext $ λ i j, hf _ _ _

end


variables (α : Type*) [comm_semiring α]
variables (R : Type*) [comm_semiring R]
variables (S : Type*) [comm_semiring S]
variables (β : Type*) [comm_semiring β]
variables [algebra α R] [algebra α S] [algebra α β] [algebra R β] [algebra S β]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def kronecker_biprod [is_scalar_tower α R β] [is_scalar_tower α S β] :
  (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) β :=
linear_map.mk₂ α
  (kronecker_map (λ r s, algebra_map R β r * algebra_map S β s))
  (kronecker_map_add_left _ $ _)
  (kronecker_map_smul_left _ $ _)
  (kronecker_map_add_right _ $ _)
  (kronecker_map_smul_right _ $ _)
-- { to_fun := λ A,
--   { to_fun := kronecker_map (λ r s, algebra_map R β r * algebra_map S β s) A,
--     map_add' := λ B₁ B₂, kronecker_map_add_right _ (by simp [mul_add]) _ _ _,
--     map_smul' := λ B₁, kronecker_map_smul_right _ sorry _ _,
--     },
--   -- begin
--   --   intro A,
--   --   use λ B, λ i j, (algebra_map R β (A i.1 j.1)) * (algebra_map S β (B i.2 j.2)),
--   --   all_goals {intros x y, ext},
--   --   { simp only [pi.add_apply, mul_add, ring_hom.map_add, dmatrix.add_apply] },
--   --   { simp only [pi.smul_apply],
--   --     rw [← is_scalar_tower.algebra_map_smul S x, id.smul_eq_mul, ring_hom.map_mul,
--   --       smul_def, (is_scalar_tower.algebra_map_apply α S β x).symm],
--   --     ring,
--   --     all_goals {exact is_scalar_tower.right} },
--   -- end,
--   map_add' := λ A₁ A₂, linear_map.ext $ λ B, begin
--     dsimp,
--     refine kronecker_map_add_left _ _ A₁ A₂ B,
--     sorry
--   end,
--   map_smul' := λ r A, linear_map.ext $ λ B, begin
--     --by {simp_rw [pi.smul_apply, ← smul_def, is_scalar_tower.smul_assoc],
--     -- refl},
--   end
--   }

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
    by { ext ⟨i, i'⟩ ⟨j, j'⟩, simp [kronecker_biprod, one_apply, algebra_map_eq_smul_one, ite_smul,
      ite_and] }

theorem kronecker_biprod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' S)
  (B' : matrix m' n' S) [is_scalar_tower α R β] [is_scalar_tower α S β] :
  kronecker_biprod α R S β (A ⬝ B) (A' ⬝ B') =
    (kronecker_biprod α R S β A A') ⬝ (kronecker_biprod α R S β B B') :=
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

theorem kronecker_biprod_assoc {T : Type*} [comm_semiring T] [algebra α T] [algebra T β]
 [is_scalar_tower α R β] [is_scalar_tower α S β] [is_scalar_tower α T β] [is_scalar_tower α β β]
 (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  @matrix.linear_equiv_index_assoc m n p _ _ _ m' n' p' _ _ _ β α _ _ _
  (kronecker_biprod α β T β (kronecker_biprod α R S β A B) C) =
    kronecker_biprod α R β β A (kronecker_biprod α S T β B C)
    :=
begin
  simp only [matrix.linear_equiv_index_assoc, kronecker_biprod, linear_map.coe_mk, id.map_eq_self,
    reindex_apply, linear_equiv.coe_mk],
  ext i j,
  simp only [equiv.prod_assoc_symm_apply, reindex_linear_equiv_apply, minor_apply, reindex_apply,
    mul_assoc],
end

end matrix_bialgebra

namespace kronecker_product

open algebra matrix matrix_bialgebra
open_locale matrix

variables (R : Type*) [comm_semiring R]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def kronecker_prod (A : matrix l m R) (B : matrix n p R) :
  matrix (l × n) (m × p) R := kronecker_biprod R R R R A B

localized "infix ` ⊗ₖ  `:100 := kronecker_prod R _" in kronecker_product
localized "notation x ` ⊗ₖ ` y:100 := kronecker_prod R x y" in kronecker_product

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
