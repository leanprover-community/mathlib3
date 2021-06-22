/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product
I (FAE) wonder if this should be in `linear_algebra/matrix` or in `data/matrix`.
-/

open tensor_product matrix
open_locale tensor_product

namespace tensor_matrix

universes u v u'

variables {α R S : Type u} [comm_semiring α]
-- variables {R S : Type u} [semiring R] [semiring S]
-- variables [algebra α R] [algebra α S]
variables {l m n p : Type v}
variables [fintype l] [fintype m] [fintype n] [fintype p]

@[simps]
def mat_tensor_bil [semiring R] [semiring S] [algebra α R] [algebra α S] :
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


-- def mat_tensor_equiv : (matrix l m R) ⊗[α] (matrix n p S) ≃ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
-- { to_fun := tensor_product.lift mat_tensor_bil,
--   map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
--   map_smul' := by simp only [forall_const, eq_self_iff_true, linear_map.map_smul],
--   inv_fun := sorry,
--   left_inv := sorry,
--   right_inv := sorry }

def kronecker_prod [semiring R] [semiring S] [algebra α R] [algebra α S] (A : matrix l m R)
  (B : matrix n p S) : matrix (l × n) (m × p) (R ⊗[α] S) := mat_tensor_bil A B

variables {α}
infix ` ⊗ₖ `:100 := kronecker_prod _
notation x ` ⊗ₖ[`:100 α `] `:0 y:100 := kronecker_prod x y

@[simp] lemma kronecker_prod_one_one [semiring R] [semiring S] [algebra α R] [algebra α S]
  [decidable_eq m] [decidable_eq n] : (1 : matrix m m R) ⊗ₖ[α] (1 : matrix n n S) =
    (1 : matrix (m × n) (m × n) (R ⊗[α] S)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_prod, boole_mul, prod.mk.inj_iff],
  simp [mat_tensor_bil, one_apply, ite_tmul, tmul_ite, ite_and],
  by_cases i = j;
  refl,
end

variables {l' m' n' p': Type v}
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

lemma kronecker_prod_mul [comm_semiring R] [comm_semiring S] [algebra α R] [algebra α S]
  (A A': matrix l m R) (B B': matrix m n R) (A' : matrix l' m' R) (B' : matrix m' n' R) :
  (A.mul B) ⊗ₖ[α] (A'.mul B') =
   ((A ⊗ₖ[α] A').mul (B ⊗ₖ[α] B') : matrix (l × l') (n × n') (R ⊗[α] R)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker_prod, mat_tensor_bil],
  simp only [sum_tmul, tmul_sum],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm],
end

lemma kronecker_prod_reindex_left [semiring R] [semiring S] [algebra α R] [algebra α S]
  (el : l ≃ l') (em : m ≃ m') (A : matrix l m R) (B : matrix n p S) :
  ((reindex_linear_equiv el em A) ⊗ₖ[α] B : matrix (l' × n) (m' × p) (R ⊗[α] S)) =
  reindex_linear_equiv (el.prod_congr (equiv.refl _)) (em.prod_congr (equiv.refl _))
  ((A ⊗ₖ[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_prod_reindex_right [semiring R] [semiring S] [algebra α R] [algebra α S]
  (en : n ≃ n') (ep : p ≃ p') (A : matrix l m R) (B : matrix n p S) :
  (A ⊗ₖ[α] (reindex_linear_equiv en ep B) : matrix (l × n') (m × p') (R ⊗[α] S)) =
  reindex_linear_equiv ((equiv.refl _).prod_congr en) ((equiv.refl _).prod_congr ep)
  ((A ⊗ₖ[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }


/--
For mathlib
-/
-- variables {β M N: Type*} [comm_ring β]

-- lemma map_mul [has_scalar β M] [has_scalar β N] (f : M →[β] N) (b : β)
--   (A : matrix m n M) : (b • A).map f = b • (A.map f) :=
-- by { ext, simp, }

-- def move_this  [add_comm_monoid M] [add_comm_monoid N] [module β M] [module β N] (f : M →[β] N) :
--   matrix m n M →[β] matrix m n N :=
-- { to_fun := λ M, M.map f,
--   map_smul' := map_mul f, }


lemma map_scalar [has_scalar α R] [has_scalar α S] (f : R →[α] S) (r : α)
  (A : matrix m n R) : (r • A).map f = r • (A.map f) :=
by { ext, simp, }

open linear_map
/-- The `linear_map` between spaces of matrices induced by a `linear_map` between their
coefficients. -/
def linear_map.map_matrix
-- [semiring R] [add_comm_monoid α] [add_comm_monoid β] [module R α] [module R β]
  [add_comm_monoid R] [add_comm_monoid S] [module α R] [module α S]
  (f : R →ₗ[α] S) : matrix m n R →ₗ[α] matrix m n S :=
{ to_fun := λ M, M.map f,
  map_add' := matrix.map_add f.to_add_monoid_hom,
  map_smul' := map_scalar f.to_mul_action_hom, }

variables [add_comm_monoid R] [add_comm_monoid S] [module α R] [module α S]
variables (f : R →ₗ[α] S) (g : R →+ S)

#check g.map_matrix

lemma linear_map.map_matrix_apply [add_comm_monoid R] [add_comm_monoid S] [module α R] [module α S]
  (f : R →ₗ[α] S) (A : matrix m n R) : f.map_matrix A = A.map f := sorry

/--
end for mathlib
-/



protected def assoc {T : Type u'} [semiring R] [semiring S] [algebra α R] [algebra α S]
  [semiring T] [algebra α T] :
  matrix (m × n × p) (m' × n' × p') (R ⊗[α] S ⊗[α] T) ≃ₗ[α]
  matrix ((m × n) × p) ((m' × n') × p') (R ⊗[α] (S ⊗[α] T)) :=
{ to_fun := λ A, reindex (equiv.prod_assoc _ _ _).symm (equiv.prod_assoc _ _ _).symm
      (map A (tensor_product.assoc _ _ _ _)),
  map_add' :=
  begin
      intros A₁ A₂,
      simp only [equiv.symm_symm, reindex_apply, linear_equiv.to_fun_eq_coe],
      have := (add_monoid_hom.map_matrix ((tensor_product.assoc α R S T).to_linear_map).to_add_monoid_hom).3
        A₁ A₂,
      simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_matrix_apply,
        linear_map.to_add_monoid_hom_coe, linear_equiv.coe_to_linear_map] at this,
      rw [this, minor_add],
      refl,
  end,
  map_smul' :=
  begin
      intros a A,
      simp only [equiv.symm_symm, reindex_apply, linear_equiv.to_fun_eq_coe],
      have := linear_map.map_matrix (tensor_product.assoc α R S T).to_linear_map a A,
      -- simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_matrix_apply,
      --   linear_map.to_add_monoid_hom_coe, linear_equiv.coe_to_linear_map] at this,
      -- rw [this, minor_add],
      -- refl,
  end,
  inv_fun := λ A, reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
      (map A (tensor_product.assoc _ _ _ _).symm),
  left_inv :=
  begin
    intros A,
    simp,
  end,
  right_inv := _ }


#check tensor_matrix.assoc

lemma kronecker_prod_assoc' {T : Type*} [comm_semiring T] [algebra α T] [semiring R] [semiring S]
  [algebra α R] [algebra α S] (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  matrix.mat_tensor_assoc ((A ⊗ₖ[α] (B ⊗ₖ[α] C)) : matrix (m × (n × p)) (m' × (n' × p'))(R ⊗[α] (S ⊗[α] T))) =
  (((A ⊗ₖ[α] B) ⊗ₖ[α] C) : matrix ((m × n) × p) ((m' × n') × p') ((R ⊗[α] S) ⊗[α] T)) := sorry
--   A.kronecker (kronecker B C) =
--   reindex_linear_equiv
--     (equiv.prod_assoc _ _ _)
--     (equiv.prod_assoc _ _ _)
--     ((A.kronecker B).kronecker C) :=
-- by { ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩, symmetry, apply mul_assoc }
-- .

-- lemma kronecker_reindex [semiring R] (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (eo : o ≃ o')
--   (M : matrix l m R) (N : matrix n o R) :
--   kronecker (reindex_linear_equiv el em M) (reindex_linear_equiv en eo N) =
--   reindex_linear_equiv
--     (el.prod_congr en) (em.prod_congr eo) (kronecker M N) :=
-- by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }



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





end tensor_matrix
