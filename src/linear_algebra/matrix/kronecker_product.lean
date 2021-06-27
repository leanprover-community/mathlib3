/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import linear_algebra.matrix
import ring_theory.tensor_product

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product
Two main definitions:
- Given a commutative semiring α and two α algebras we define kronecker_prod₂, denoted ⊗₂[α], as
the bilinear Kronecker product
⊗₂[α] : matrix (l n R) →ₗ[α] (matrix m p S) →ₗ[α] (matrix (l × m) (n × p) (R ⊗[α] S).
- In the special case when α=R=S, we compose ⊗₂[α] with the canoical equivalence α ⊗[α] α ≃ α to
define kronecker_prod, denoted by ⊗ₖ as the α-linear map
⊗ₖ  : matrix (l n α) →ₗ[α] (matrix m p α) →ₗ[α] (matrix (l × m) (n × p) (α).

For both products, we prove that it is associative (in theorems `kronecker_prod₂_assoc` and
`prod_assoc`, respectively) as well as the so-called `mixed-product property (in theorems
`kronecker_prod₂_mul` and `prod_mul`, respectively).

I (FAE) wonder if this file should be in `linear_algebra/matrix` or rather in `data/matrix`.
-/

universes u v u'

namespace tensor_matrix

open tensor_product matrix
open_locale tensor_product


variables {α R S : Type u} [comm_semiring α]
variables {l m n p l' m' n' p' : Type v}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def matrix_tensor_bil [add_comm_monoid R] [add_comm_monoid S] [module α R] [module α S] :
  (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
{ to_fun :=
  begin
    intro A,
    use λ B, λ i j, A i.1 j.1 ⊗ₜ[α] B i.2 j.2,
    all_goals {intros _ _, ext},
    apply tmul_add,
    apply tmul_smul,
  end,
  map_add' := λ _ _, by {simp only [linear_map.coe_mk, dmatrix.add_apply], simp_rw add_tmul, refl},
  map_smul' := λ _ _, by {simp only [pi.smul_apply], simp_rw [smul_tmul, tmul_smul], refl},
  }

lemma assoc_aux {T : Type u'} [add_comm_monoid T] [module α T] [add_comm_monoid R]
  [add_comm_monoid S] [module α R] [module α S] :
  ⇑((tensor_product.assoc α R S T).symm) ∘ ⇑(tensor_product.assoc α R S T) = id ∧
    ⇑(tensor_product.assoc α R S T) ∘ ⇑((tensor_product.assoc α R S T).symm) = id :=
  begin
    split;
    all_goals {ext, simp only [id.def, function.comp_app, linear_equiv.symm_apply_apply,
      linear_equiv.apply_symm_apply]},
  end

protected
def assoc {T : Type u'} [add_comm_monoid T] [module α T] [add_comm_monoid R] [add_comm_monoid S]
  [module α R] [module α S] : matrix ((m × n) × p) ((m' × n') × p') (R ⊗[α] S ⊗[α] T) ≃ₗ[α]
    matrix (m × n × p) (m' × n' × p') (R ⊗[α] (S ⊗[α] T)) :=
{ to_fun := λ A, reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
      (map A (tensor_product.assoc _ _ _ _)),
  map_add' :=
  begin
      intros A₁ A₂,
      have := (add_monoid_hom.map_matrix
        ((tensor_product.assoc α R S T).to_linear_map).to_add_monoid_hom).3 A₁ A₂,
      simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_matrix_apply,
        linear_map.to_add_monoid_hom_coe, linear_equiv.coe_to_linear_map] at this,
      simp only [equiv.symm_symm, reindex_apply, linear_equiv.to_fun_eq_coe, this, minor_add,
        pi.add_apply],
  end,
  map_smul' :=
  begin
      intros a A,
      have := (linear_map.map_matrix (tensor_product.assoc α R S T).to_linear_map).3 a A,
      simp only [linear_map.to_fun_eq_coe, linear_map.map_matrix_apply,
      linear_equiv.coe_to_linear_map] at this,
      simp only [equiv.symm_symm, reindex_apply, linear_equiv.to_fun_eq_coe, this, minor_smul,
        pi.smul_apply],
  end,
  inv_fun := λ A, reindex (equiv.prod_assoc _ _ _).symm (equiv.prod_assoc _ _ _).symm
      (map A (tensor_product.assoc _ _ _ _).symm),
  left_inv := λ _, by {simp only [equiv.symm_symm, reindex_apply, minor_map, minor_minor, map_map,
    assoc_aux, minor_id_id, equiv.symm_comp_self], refl},
  right_inv := λ _, by {simp only [equiv.symm_symm, reindex_apply, minor_map, minor_minor, map_map,
    assoc_aux, minor_id_id, equiv.self_comp_symm], refl},
  }

section general_kronecker_product

/-- For the special case where α=R=S, see kronecker_prod.prod below. -/

def kronecker_prod₂ [add_comm_monoid R] [add_comm_monoid S] [module α R] [module α S]
  (A : matrix l m R) (B : matrix n p S) : matrix (l × n) (m × p) (R ⊗[α] S) :=
matrix_tensor_bil A B

infix ` ⊗₂  `:100 := kronecker_prod₂ _
notation x ` ⊗₂[`:100 α `] `:0 y:100 := kronecker_prod₂ x y


lemma kronecker_prod₂_reindex_left [semiring R] [semiring S] [algebra α R] [algebra α S]
  (eₗ : l ≃ l') (eₘ : m ≃ m') (A : matrix l m R) (B : matrix n p S) :
  ((reindex_linear_equiv eₗ eₘ A) ⊗₂[α] B : matrix (l' × n) (m' × p) (R ⊗[α] S)) =
  reindex_linear_equiv (eₗ.prod_congr (equiv.refl _)) (eₘ.prod_congr (equiv.refl _))
  ((A ⊗₂[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_prod₂_reindex_right [semiring R] [semiring S] [algebra α R] [algebra α S]
  (eₙ : n ≃ n') (eₚ : p ≃ p') (A : matrix l m R) (B : matrix n p S) :
  (A ⊗₂[α] (reindex_linear_equiv eₙ eₚ B) : matrix (l × n') (m × p') (R ⊗[α] S)) =
  reindex_linear_equiv ((equiv.refl _).prod_congr eₙ) ((equiv.refl _).prod_congr eₚ)
  ((A ⊗₂[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_prod₂_one_one [semiring R] [semiring S] [algebra α R] [algebra α S]
  [decidable_eq m] [decidable_eq n] : (1 : matrix m m R) ⊗₂[α] (1 : matrix n n S) =
    (1 : matrix (m × n) (m × n) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, simp [kronecker_prod₂,
      boole_mul, matrix_tensor_bil, one_apply, ite_tmul, tmul_ite, ite_and,
      algebra.tensor_product.one_def, prod.mk.inj_iff, eq_self_iff_true, linear_map.coe_mk] }

theorem kronecker_prod₂_mul [comm_semiring R] [comm_semiring S] [algebra α R] [algebra α S]
  (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' S) (B' : matrix m' n' S) :
  (A.mul B) ⊗₂[α] (A'.mul B') =
   ((A ⊗₂[α] A').mul (B ⊗₂[α] B') : matrix (l × l') (n × n') (R ⊗[α] S)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker_prod₂, matrix_tensor_bil],
  simp only [sum_tmul, tmul_sum],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm],
end

theorem kronecker_prod₂_assoc {T : Type*} [comm_semiring T] [algebra α T] [semiring R] [semiring S]
  [algebra α R] [algebra α S] (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  tensor_matrix.assoc ((A ⊗₂[α] B : matrix (m × n) (m' × n') (R ⊗[α] S)) ⊗₂[α] C) =
    (A ⊗₂[α] (B ⊗₂[α] C)) := rfl

end general_kronecker_product

-- for mathlib
-- add also the equiv tra tipi?


def linear_equiv.map_matrix [semiring α] [add_comm_monoid R] [add_comm_monoid S]
  [module α R] [module α S] (f : R ≃ₗ[α] S) : matrix m n R ≃ₗ[α] matrix m n S :=
{ to_fun := λ M, M.map f,
  map_add' := matrix.map_add f.to_linear_map.to_add_monoid_hom,
  map_smul' := matrix.map_smul f.to_linear_map.to_mul_action_hom,
  inv_fun := λ M, M.map f.symm,
  left_inv := λ M, by {ext, simp only [function.comp_app,
    linear_equiv.symm_apply_apply, map_apply]},
  right_inv := λ M, by {ext, simp only [function.comp_app,
    linear_equiv.apply_symm_apply, map_apply]}, }

end tensor_matrix

namespace kronecker_product

open tensor_product matrix tensor_matrix algebra.tensor_product
open_locale tensor_product

variables {R : Type*} [comm_semiring R]
variables {l m n p l' m' n' p' : Type v}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def prod (A : matrix l m R) (B : matrix n p R) : matrix (l × n) (m × p) R :=
(matrix_tensor_bil A B).map (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom

infix ` ⊗ₖ  `:100 := prod _
notation x ` ⊗ₖ ` y:100 := prod x y

@[simp] lemma kronecker_prod₂_prod (A : matrix l m R) (B : matrix n p R) :
  (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
    (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom = A ⊗ₖ B :=
rfl

@[simp] lemma prod_kronecker_prod₂ (A : matrix l m R) (B : matrix n p R) :
  A ⊗ₖ B = (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
  (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom :=
rfl

lemma prod_reindex_left (eₗ : l ≃ l') (eₘ : m ≃ m') (A : matrix l m R) (B : matrix n p R)
  : (reindex_linear_equiv eₗ eₘ A) ⊗ₖ B =
    reindex_linear_equiv (eₗ.prod_congr (equiv.refl _)) (eₘ.prod_congr (equiv.refl _)) ((A ⊗ₖ B)) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma prod_reindex_right (eₙ : n ≃ n') (eₚ : p ≃ p') (A : matrix l m R) (B : matrix n p R)
  : (A ⊗ₖ (reindex_linear_equiv eₙ eₚ B) =
    reindex_linear_equiv ((equiv.refl _).prod_congr eₙ) ((equiv.refl _).prod_congr eₚ) (A ⊗ₖ B)) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

@[simp] lemma prod_one_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m R) ⊗ₖ (1 : matrix n n R) = 1 := by simp only [kronecker_prod₂_one_one,
    ring_hom_map_one, prod_kronecker_prod₂]

theorem prod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' R)
  (B' : matrix m' n' R) : (A.mul B) ⊗ₖ (A'.mul B') = (A ⊗ₖ A').mul (B ⊗ₖ B') :=
begin
  simp only [prod_kronecker_prod₂],
  rw [← @matrix.map_mul _ _ _ _ _ _ (R ⊗ R) R _ (A ⊗₂[R] A') (B ⊗₂[R] B') _
    (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom, kronecker_prod₂_mul],
end



--TO ADD
-- def algebra_equiv.map_matrix [semiring R] [add_comm_monoid α] [add_comm_monoid β]
--   [module R α] [module R β] (f : α ≃ₗ[R] β) : matrix m n α ≃ₗ[R] matrix m n β :=
-- { to_fun := λ M, M.map f,
--   map_add' := matrix.map_add f.to_add_monoid_hom,
--   map_smul' := matrix.map_smul f.to_mul_action_hom, }

--

protected def assoc : matrix ((m × n) × p) ((m' × n') × p') R ≃ₗ[R]
    matrix (m × n × p) (m' × n' × p') R :=
begin
have f₁ := ((algebra.tensor_product.lid R (R ⊗ R)).to_linear_equiv).trans
  (algebra.tensor_product.lid R R).to_linear_equiv,
have f₂ := ((algebra.tensor_product.rid R (R ⊗ R)).to_linear_equiv).trans
  ((algebra.tensor_product.lid R R).to_linear_equiv),
have g₁ := linear_equiv.map_matrix f₁,
have g₂ := linear_equiv.map_matrix f₂,
rotate, use (( m × n) × p), use ((m' × n') × p'), sorry, sorry,
use (m × n × p), use (m' × n' × p'), sorry, sorry,
-- have h := @linear_equiv.map_matrix R (R ⊗ (R ⊗ R)) R _ (m × n × p) (m' × n' × p') _ _ _ _ _ _ _
--   ((algebra.tensor_product.lid R (R ⊗ R)).to_linear_equiv),
have h2 := (@tensor_matrix.assoc R R R _ m n p m' n' p' _ _ _ _ _ _ R _ _ _ _ _ _),
-- ((algebra.tensor_product.lid R R).to_linear_equiv),
-- exact (@tensor_matrix.assoc R R R _ m n p m' n' p' _ _ _ _ _ _ R _ _ _ _ _ _),
end

-- theorem prod_assoc (A : matrix m m' R) (B : matrix n n' R) (C : matrix p p' R) :
--   --tensor_matrix.assoc
--   (A ⊗ₖ B) ⊗ₖ C = A ⊗ₖ (B ⊗ₖ C) :=
--     begin
--       refl,
--     end
--     --rfl

-- theorem prod_assoc

-- theorem kronecker_prod₂_assoc {T : Type*} [comm_semiring T] [algebra α T] [semiring R] [semiring S]
--   [algebra α R] [algebra α S] (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
--   tensor_matrix.assoc ((A ⊗₂[α] B : matrix (m × n) (m' × n') (R ⊗[α] S)) ⊗₂[α] C) =
--     (A ⊗₂[α] (B ⊗₂[α] C)) := rfl

--for LTE
-- lemma kronecker_assoc [semiring R] (A : matrix m m' R) (B : matrix n n' R) (C : matrix o o' R) :
--   (A.kronecker B).kronecker C =
--   reindex_linear_equiv
--     (equiv.prod_assoc _ _ _).symm
--     (equiv.prod_assoc _ _ _).symm
--     (A.kronecker (kronecker B C)) :=
-- by { ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩, apply mul_assoc }

-- lemma kronecker_assoc' [semiring R] (A : matrix m m' R) (B : matrix n n' R) (C : matrix o o' R) :
--   A.kronecker (kronecker B C) =
--   reindex_linear_equiv
--     (equiv.prod_assoc _ _ _)
--     (equiv.prod_assoc _ _ _)
--     ((A.kronecker B).kronecker C) :=
-- by { ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩, symmetry, apply mul_assoc }

-- def


end kronecker_product
