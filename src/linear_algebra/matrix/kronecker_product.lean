import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product

-/

open tensor_product
open_locale tensor_product

namespace matrix

variables {α : Type*} [comm_semiring α]
variables {R S : Type*} [comm_semiring R] [comm_semiring S]
variables [algebra α R] [algebra α S]
variables {l m n p : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]

def matrix_tensor_bil : (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
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

def matrix_tensor_equiv : (matrix l m R) ⊗[α] (matrix n p S) ≃ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
{ to_fun := tensor_product.lift matrix_tensor_bil,
  map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
  map_smul' := by simp only [forall_const, eq_self_iff_true, linear_map.map_smul],
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

def kronecker_prod (A : matrix l m R) (B : matrix n p S) :
  matrix (l × n) (m × p) (R ⊗[α] S) := matrix_tensor_bil A B

variables {α}
infix ` ⊗ₖ `:100 := kronecker_prod _
notation x ` ⊗ₖ[`:100 α `] `:0 y:100 := kronecker_prod x y

variables {l' m' n': Type*}
variables [fintype l'] [fintype m'] [fintype n']

lemma kronecker_prod_mul (A A': matrix l m R) (B B': matrix m n R) (A' : matrix l' m' R)
  (B' : matrix m' n' R) : (A.mul B) ⊗ₖ[α] (A'.mul B') =
    ((A ⊗ₖ[α] A').mul (B ⊗ₖ[α] B') : matrix (l × l') (n × n') (R ⊗[α] R)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker_prod, matrix_tensor_bil],
  simp only [sum_tmul, tmul_sum],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm],
end

@[simp] lemma kronecker_prod_one_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m R) ⊗ₖ[α] (1 : matrix n n S) =  (1 : matrix (m × n) (m × n) (R ⊗[α] S)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_prod, one_apply, boole_mul, prod.mk.inj_iff],
  convert (@ite_and _ (i = j) (i' = j') _ _ (1 : R) (0 : R)).symm,
  convert (@ite_and _ (i = j) (i' = j') _ _ (1 : S) (0 : S)).symm,
end
-- .

-- lemma kronecker_reindex [semiring R] (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (eo : o ≃ o')
--   (M : matrix l m R) (N : matrix n o R) :
--   kronecker (reindex_linear_equiv el em M) (reindex_linear_equiv en eo N) =
--   reindex_linear_equiv
--     (el.prod_congr en) (em.prod_congr eo) (kronecker M N) :=
-- by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

-- lemma kronecker_reindex_left [semiring R] (el : l ≃ l') (em : m ≃ m') (M : matrix l m R) (N : matrix n o R) :
--   kronecker (reindex_linear_equiv el em M) N =
--   reindex_linear_equiv
--     (el.prod_congr (equiv.refl _)) (em.prod_congr (equiv.refl _)) (kronecker M N) :=
-- by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

-- lemma kronecker_reindex_right [semiring R] (en : n ≃ n') (eo : o ≃ o') (M : matrix l m R) (N : matrix n o R) :
--   kronecker M (reindex_linear_equiv en eo N) =
--   reindex_linear_equiv
--     ((equiv.refl _).prod_congr en) ((equiv.refl _).prod_congr eo) (kronecker M N) :=
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





end matrix
