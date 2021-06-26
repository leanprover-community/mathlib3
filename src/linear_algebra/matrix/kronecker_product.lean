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

/-All this takes place in a separate namespace, concerning the relation between tensors and
matrices
-/

universes u v u'

variables {α R S : Type u} [comm_semiring α]
variables {l m n p : Type v}
variables [fintype l] [fintype m] [fintype n] [fintype p]

@[simps]
def matrix_tensor_bil [semiring R] [semiring S] [algebra α R] [algebra α S] :
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
  (B : matrix n p S) : matrix (l × n) (m × p) (R ⊗[α] S) := matrix_tensor_bil A B

variables {α}
infix ` ⊗ₖ `:100 := kronecker_prod _
notation x ` ⊗ₖ[`:100 α `] `:0 y:100 := kronecker_prod x y

@[simp] lemma kronecker_prod_one_one [semiring R] [semiring S] [algebra α R] [algebra α S]
  [decidable_eq m] [decidable_eq n] : (1 : matrix m m R) ⊗ₖ[α] (1 : matrix n n S) =
    (1 : matrix (m × n) (m × n) (R ⊗[α] S)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_prod, boole_mul, prod.mk.inj_iff],
  simp [matrix_tensor_bil, one_apply, ite_tmul, tmul_ite, ite_and],
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
  dsimp [mul_apply, kronecker_prod, matrix_tensor_bil],
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

lemma aux {T : Type u'} [semiring T] [algebra α T] [semiring R] [semiring S] [algebra α R]
  [algebra α S] : ⇑((tensor_product.assoc α R S T).symm) ∘ ⇑(tensor_product.assoc α R S T) = id ∧
  ⇑(tensor_product.assoc α R S T) ∘ ⇑((tensor_product.assoc α R S T).symm) = id :=
  begin
    split;
    all_goals {ext, simp only [id.def, function.comp_app, linear_equiv.symm_apply_apply,
      linear_equiv.apply_symm_apply]},
  end


protected
def assoc {T : Type u'} [semiring T] [algebra α T] [semiring R] [semiring S] [algebra α R]
  [algebra α S] : matrix ((m × n) × p) ((m' × n') × p') (R ⊗[α] S ⊗[α] T) ≃ₗ[α]
  matrix (m × n × p) (m' × n' × p') (R ⊗[α] (S ⊗[α] T)) :=
{ to_fun :=λ A, reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
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
    aux, minor_id_id, equiv.symm_comp_self], refl},
  right_inv := λ _, by {simp only [equiv.symm_symm, reindex_apply, minor_map, minor_minor, map_map,
    aux, minor_id_id, equiv.self_comp_symm], refl},
  }


lemma kronecker_prod_assoc {T : Type*} [comm_semiring T] [algebra α T] [semiring R] [semiring S]
  [algebra α R] [algebra α S] (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  tensor_matrix.assoc ((A ⊗ₖ[α] B : matrix (m × n) (m' × n') (R ⊗[α] S)) ⊗ₖ[α] C) =
    (A ⊗ₖ[α] (B ⊗ₖ[α] C)) := rfl

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
