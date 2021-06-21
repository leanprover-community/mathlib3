import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product

-/

open tensor_product
open_locale tensor_product

namespace matrix

variables {α : Type*} [comm_semiring α]
variables {R S : Type*} [semiring R] [semiring S]
variables [algebra α R] [algebra α S]
variables {l m n p : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]

@[simps]
def mat_tensor_bil : (matrix l m R) →ₗ[α] (matrix n p S) →ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
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

def mat_tensor_equiv : (matrix l m R) ⊗[α] (matrix n p S) ≃ₗ[α] matrix (l × n) (m × p) (R ⊗[α] S) :=
{ to_fun := tensor_product.lift mat_tensor_bil,
  map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
  map_smul' := by simp only [forall_const, eq_self_iff_true, linear_map.map_smul],
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

def kronecker_prod (A : matrix l m R) (B : matrix n p S) :
  matrix (l × n) (m × p) (R ⊗[α] S) := mat_tensor_bil A B

variables {α}
infix ` ⊗ₖ `:100 := kronecker_prod _
notation x ` ⊗ₖ[`:100 α `] `:0 y:100 := kronecker_prod x y

@[simp] lemma kronecker_prod_one_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m R) ⊗ₖ[α] (1 : matrix n n S) =  (1 : matrix (m × n) (m × n) (R ⊗[α] S)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_prod, boole_mul, prod.mk.inj_iff],
  simp [mat_tensor_bil, one_apply, ite_tmul, tmul_ite, ite_and],
  by_cases i = j;
  refl,
end

variables {l' m' n' p': Type*}
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

lemma kronecker_prod_mul [comm_semiring R] [comm_semiring S] (A A': matrix l m R) (B B': matrix m n R) (A' : matrix l' m' R)
  (B' : matrix m' n' R) : (A.mul B) ⊗ₖ[α] (A'.mul B') =
    ((A ⊗ₖ[α] A').mul (B ⊗ₖ[α] B') : matrix (l × l') (n × n') (R ⊗[α] R)) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker_prod, mat_tensor_bil],
  simp only [sum_tmul, tmul_sum],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm],
end

lemma kronecker_prod_reindex_left (el : l ≃ l') (em : m ≃ m') (A : matrix l m R) (B : matrix n p S) :
  ((reindex_linear_equiv el em A) ⊗ₖ[α] B : matrix (l' × n) (m' × p) (R ⊗[α] S)) =
  reindex_linear_equiv (el.prod_congr (equiv.refl _)) (em.prod_congr (equiv.refl _))
  ((A ⊗ₖ[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_prod_reindex_right (en : n ≃ n') (ep : p ≃ p') (A : matrix l m R) (B : matrix n p S) :
  (A ⊗ₖ[α] (reindex_linear_equiv en ep B) : matrix (l × n') (m × p') (R ⊗[α] S)) =
  reindex_linear_equiv ((equiv.refl _).prod_congr en) ((equiv.refl _).prod_congr ep)
  ((A ⊗ₖ[α] B) : matrix (l × n) (m × p) (R ⊗[α] S)) := by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

protected def mat_tensor_assoc [T : Type*] [comm_semiring T] [algebra α T] :
  matrix (m × (n × p)) (m' × (n' × p')) (R ⊗[α] (S ⊗[α] T)) ≃ₗ[α]
  matrix ((m × n) × p) ((m' × n') × p') (R ⊗[α] S ⊗[α] T) :=
begin
  sorry,
  -- refine linear_equiv.of_linear
  --   (lift $ lift $ comp (lcurry R _ _ _) $ mk _ _ _)
  --   (lift $ comp (uncurry R _ _ _) $ curry $ mk _ _ _)
  --   (mk_compr₂_inj $ linear_map.ext $ λ m, ext $ λ n p, _)
  --   (mk_compr₂_inj $ flip_inj $ linear_map.ext $ λ p, ext $ λ m n, _);
  -- repeat { rw lift.tmul <|> rw compr₂_apply <|> rw comp_apply <|>
  --   rw mk_apply <|> rw flip_apply <|> rw lcurry_apply <|>
  --   rw uncurry_apply <|> rw curry_apply <|> rw id_apply }
end

variables {T : Type*} [comm_semiring T] [algebra α T]
#check matrix.mat_tensor_assoc

lemma kronecker_prod_assoc' [T : Type*] [comm_semiring T] [algebra α T] (A : matrix m m' R)
 (B : matrix n n' S) (C : matrix p p' T) :
 matrix.assoc ((A ⊗ₖ[α] (B ⊗ₖ[α] C)) : matrix (m × (n × p)) (m' × (n' × p')) (R ⊗[α] (S ⊗[α] T))) =
 (((A ⊗ₖ[α] B) ⊗ₖ[α] C) : matrix ((m × n) × p) ((m' × n') × p') ((R ⊗[α] S) ⊗[α] T)) :=
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





end matrix
