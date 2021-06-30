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

universes u v v' u'

namespace matrix_bialgebra

open algebra matrix function
open_locale matrix big_operators

variables {α : Type*}
variables {R : Type*}
variables {S : Type*}
variables {β : Type*}
variables [comm_semiring α] [comm_semiring R] [comm_semiring S] [comm_semiring β]
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

lemma foo [A : finset R] [B : finset S] (f : R → α) (g : S → α) :
  ∑ a in A, (λ a, ∑ b in B,  (f a + g b)) = ∑ c in B, (λ C, ∑ d in A,  (f d + g c)) :=
  begin
    squeeze_simp,
  end

theorem kronecker_biprod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' S)
  (B' : matrix m' n' S) : kronecker_biprod h_Rβ h_Sβ (A ⬝ B) (A' ⬝ B') =
   (kronecker_biprod h_Rβ h_Sβ A A') ⬝ (kronecker_biprod h_Rβ h_Sβ B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [mul_apply, kronecker_biprod, algebra_map_eq_smul_one, mul_one, algebra.mul_smul_comm,
    linear_map.coe_mk, algebra.smul_mul_assoc, ← finset.univ_product_univ, finset.sum_product],
  simp_rw [finset.sum_smul, finset.smul_sum, ← smul_eq_mul],
  repeat {apply finset.sum_congr, refl, intros _ _,},
  rw is_scalar_tower.smul_assoc,
  -- rw is_scalar_tower.smul_assoc,
  rw [id.smul_eq_mul (A' i' x_1) (B' x_1 j')],
  rw ← algebra_map_eq_smul_one,
  rw ← algebra_map_eq_smul_one,
  rw [smul_def (B x j) _],
  rw [smul_def (B x j) _],
  rw [smul_def (A' i' x_1) _],
  simp only [ring_hom.map_mul],
  ring,
end

theorem kronecker_prod₂_assoc {T : Type*} [comm_semiring T] [algebra α T] [semiring R] [semiring S]
  [algebra α R] [algebra α S] (A : matrix m m' R) (B : matrix n n' S) (C : matrix p p' T) :
  tensor_matrix.assoc ((A ⊗₂[α] B : matrix (m × n) (m' × n') (R ⊗[α] S)) ⊗₂[α] C) =
    (A ⊗₂[α] (B ⊗₂[α] C)) := rfl

end tensor_matrix

namespace kronecker_product

open tensor_product matrix tensor_matrix --togliere tensor_product e mettere algebra (pure su)
open_locale tensor_product

variables {R : Type*} [comm_semiring R]
variables {l m n p l' m' n' p' : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p]
variables [fintype l'] [fintype m'] [fintype n'] [fintype p']

def prod (A : matrix l m R) (B : matrix n p R) : matrix (l × n) (m × p) R :=
(matrix_tensor_bil A B).map (tensor_product.lid R R)--.to_alg_hom.to_ring_hom

-- infix ` ⊗ₖ  `:100 := prod _
-- notation x ` ⊗ₖ ` y:100 := prod x y

@[simp] lemma prod_ext (A : matrix l m R) (B : matrix n p R) (i : l × n) (j: m × p) :
  (prod A B) i j = A i.1 j.1 * B i.2 j.2 := by simp only [prod, matrix_tensor_bil,
    tensor_product.lid_tmul, algebra.id.smul_eq_mul, linear_map.coe_mk, map_apply, lid_tmul]

-- @[simp] lemma prod_ext (A : matrix l m R) (B : matrix n p R) (i : l × n) (j: m × p) :
--   (A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2 := by simp only [prod, matrix_tensor_bil,
--     tensor_product.lid_tmul, algebra.id.smul_eq_mul, linear_map.coe_mk, map_apply, lid_tmul]


-- @[simp] lemma kronecker_prod₂_prod (A : matrix l m R) (B : matrix n p R) :
--   (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
--     (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom = A ⊗ₖ B :=
-- rfl

-- @[simp] lemma prod_kronecker_prod₂ (A : matrix l m R) (B : matrix n p R) :
--   A ⊗ₖ B = (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
--   (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom :=
-- rfl

@[simp] lemma prod_kronecker_prod₂ (A : matrix l m R) (B : matrix n p R) :
  prod A B = (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
  (algebra.tensor_product.lid R R).to_linear_equiv := rfl

@[simp] lemma prod_kronecker_prod₂' (A : matrix l m R) (B : matrix n p R) :
  prod A B = (A ⊗₂[R] B : matrix (l × n) (m × p) (R ⊗[R] R)).map
  (tensor_product.lid R R) := rfl


-- lemma prod_reindex_left (eₗ : l ≃ l') (eₘ : m ≃ m') (A : matrix l m R) (B : matrix n p R)
--   : (reindex_linear_equiv eₗ eₘ A) ⊗ₖ B =
--     reindex_linear_equiv (eₗ.prod_congr (equiv.refl _)) (eₘ.prod_congr (equiv.refl _)) ((A ⊗ₖ B)) :=
-- by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

-- lemma prod_reindex_right (eₙ : n ≃ n') (eₚ : p ≃ p') (A : matrix l m R) (B : matrix n p R)
--   : (A ⊗ₖ (reindex_linear_equiv eₙ eₚ B) =
--     reindex_linear_equiv ((equiv.refl _).prod_congr eₙ) ((equiv.refl _).prod_congr eₚ) (A ⊗ₖ B)) :=
-- by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

-- @[simp] lemma prod_one_one [decidable_eq m] [decidable_eq n] :
--   (1 : matrix m m R) ⊗ₖ (1 : matrix n n R) = 1 := by simp only [kronecker_prod₂_one_one,
--     ring_hom_map_one, prod_kronecker_prod₂]

-- theorem prod_mul (A : matrix l m R) (B : matrix m n R) (A' : matrix l' m' R)
--   (B' : matrix m' n' R) : (A.mul B) ⊗ₖ (A'.mul B') = (A ⊗ₖ A').mul (B ⊗ₖ B') :=
-- begin
--   simp only [prod_kronecker_prod₂],
--   rw [← @matrix.map_mul _ _ _ _ _ _ (R ⊗ R) R _ (A ⊗₂[R] A') (B ⊗₂[R] B') _
--     (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom, kronecker_prod₂_mul],
-- end



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
have g₁ := @linear_equiv.map_matrix _ _ _ _ (m × n × p) (m' × n' × p') _ _ _ _ _ _ _ f₁,
have g₂ := @linear_equiv.map_matrix _ _ _ _ ((m × n) × p) ((m' × n') × p') _ _ _ _ _ _ _ f₂,
have h := (@tensor_matrix.assoc R R R _ m n p m' n' p' _ _ _ _ _ _ R _ _ _ _ _ _),
use g₂.symm.trans (h.trans g₁),
end

protected def assoc' : matrix ((m × n) × p) ((m' × n') × p') R ≃ₗ[R]
    matrix (m × n × p) (m' × n' × p') R :=
begin
have f₁ := (tensor_product.lid R (R ⊗ R)).trans (tensor_product.lid R R),
have f₂ := (tensor_product.rid R (R ⊗ R)).trans (tensor_product.lid R R),
have g₁ := @linear_equiv.map_matrix _ _ _ _ (m × n × p) (m' × n' × p') _ _ _ _ _ _ _ f₁,
have g₂ := @linear_equiv.map_matrix _ _ _ _ ((m × n) × p) ((m' × n') × p') _ _ _ _ _ _ _ f₂,
have h := (@tensor_matrix.assoc R R R _ m n p m' n' p' _ _ _ _ _ _ R _ _ _ _ _ _),
use g₂.symm.trans (h.trans g₁),
end

-- [prod, matrix_tensor_bil,
--     tensor_product.lid_tmul, algebra.id.smul_eq_mul,
--linear_map.coe_mk, map_apply, lid_tmul]
theorem prod_assoc' (A : matrix m m' R) (B : matrix n n' R) (C : matrix p p' R) :
  -- kronecker_product.assoc (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kronecker_product.assoc' (prod (prod A B) C) = prod A (prod B C) :=
  -- by { ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩, symmetry, apply mul_assoc }
    begin
      rw kronecker_product.assoc',
      rw prod_kronecker_prod₂',
      rw prod_kronecker_prod₂',
      rw prod_kronecker_prod₂',
      rw prod_kronecker_prod₂',
      simp [equiv.trans_apply],
      rw ← linear_equiv.map_matrix_symm,
      rw foo1,
      rw linear_equiv.map_matrix_trans,
      rw linear_equiv.map_matrix_trans,--inutile?
      rw linear_equiv.map_matrix_symm,
      simp only [linear_equiv.trans_apply, alg_equiv.to_linear_equiv_symm],
      -- let φₘₙ : matrix ((m × n) × p) ((m' × n') × p') R ≃ₗ matrix ((m × n) × p) ((m' × n') × p') (R ⊗ R)
      --  := (linear_equiv.map_matrix (algebra.tensor_product.lid R R).to_linear_equiv).symm,
      -- have tt := --(linear_equiv.map_matrix (tensor_product.lid R R)).symm
      -- (kronecker_prod₂ ((kronecker_prod₂ A B).map (tensor_product.lid R R)) C).map (tensor_product.lid R R),
      -- have : (linear_equiv.map_matrix (algebra.tensor_product.lid R R).to_linear_equiv).symm
      have : (linear_equiv.map_matrix (tensor_product.lid R R)).symm
        ((kronecker_prod₂ ((kronecker_prod₂ A B).map (tensor_product.lid R R)) C).map (tensor_product.lid R R)) =
         kronecker_prod₂ ((kronecker_prod₂ A B).map ⇑(tensor_product.lid R R)) C,
        --  kronecker_prod₂ ((kronecker_prod₂ A B).map ⇑((algebra.tensor_product.lid R R).to_linear_equiv)) C,
         sorry,
      rw this,
      rw [@rid_symm_apply R _ (R ⊗ R) _ (kronecker_prod₂ ((kronecker_prod₂ A B).map ⇑(tensor_product.lid R R)) C)],
    end

theorem prod_assoc (A : matrix m m' R) (B : matrix n n' R) (C : matrix p p' R) :
  -- kronecker_product.assoc (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kronecker_product.assoc (prod (prod A B) C) = prod A (prod B C) :=
  -- by { ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩, symmetry, apply mul_assoc }
    begin
      rw kronecker_product.assoc,
      rw prod_kronecker_prod₂,
      rw prod_kronecker_prod₂,
      rw prod_kronecker_prod₂,
      rw prod_kronecker_prod₂,
      simp [equiv.trans_apply],
      rw ← linear_equiv.map_matrix_symm,
      rw foo1,
      rw linear_equiv.map_matrix_trans,
      rw linear_equiv.map_matrix_trans,--inutile?
      rw linear_equiv.map_matrix_symm,
      simp only [linear_equiv.trans_apply, alg_equiv.to_linear_equiv_symm],
      have : (linear_equiv.map_matrix (algebra.tensor_product.lid R R).to_linear_equiv).symm
        ((kronecker_prod₂ ((kronecker_prod₂ A B).map (algebra.tensor_product.lid R R).to_linear_equiv) C).map (algebra.tensor_product.lid R R).to_linear_equiv)
          =
         kronecker_prod₂ ((kronecker_prod₂ A B).map ⇑((algebra.tensor_product.lid R R).to_linear_equiv)) C, sorry,
      rw this,
      rw rid_symm_apply,

      -- rw [linear_equiv.symm_apply_apply (linear_equiv.map_matrix (algebra.tensor_product.lid R R).to_linear_equiv) (kronecker_prod₂ ((kronecker_prod₂ A B).map ⇑((algebra.tensor_product.lid R R).to_linear_equiv)) C)],
      -- ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩,
--     convert_to kronecker_product.assoc ((kronecker_prod₂ ((kronecker_prod₂ A B).map
-- ((algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map)) C).map
--     ((algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map))
--   = (kronecker_prod₂ A (prod B C)).map
--   ((algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map),
      convert_to kronecker_product.assoc (
        linear_map.map_matrix (algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map (
          kronecker_prod₂
(linear_map.map_matrix ((algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map) ( kronecker_prod₂ A B))
                          C) )
          =
          linear_map.map_matrix
        ((algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map )
         (kronecker_prod₂ A (prod B C)),
      have hc := congr_arg (linear_map.map_matrix
        (algebra.tensor_product.lid R R).to_linear_equiv.to_linear_map),
        rotate, use (m × n) × p, use (m' × n') × p', apply_instance, apply_instance,
        -- use kronecker_prod₂ A (prod B C),
        use kronecker_prod₂ (prod A B) C, sorry,
        -- have w:= (kronecker_prod₂ A (prod B C)),
        have t:= kronecker_prod₂_assoc A B C,
      apply hc,
      -- rw ← kronecker_prod₂_assoc,
      have hj : function.injective (algebra.tensor_product.lid R R).to_alg_hom.to_ring_hom, sorry,

      ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩,
      -- rw prod_ext,
      -- rw prod_ext,
      -- rw kronecker_product.assoc,
      -- rw linear_equiv.trans,
      -- rw linear_equiv.map_matrix,
      -- -- simp,
      -- rw algebra.tensor_product.lid,
      --   -- ((algebra.tensor_product.lid R (R ⊗ R)).to_linear_equiv.trans (algebra.tensor_product.lid R R).to_linear_equiv),
      -- symmetry,
      -- simp [prod,
      --   kronecker_product.assoc,
      --   matrix_tensor_bil,
      --   tensor_product.lid_tmul,
      --   algebra.id.smul_eq_mul,
      --   linear_map.coe_mk,
      --   map_apply,
      --   lid_tmul, rid_tmul,
      --   mul_assoc],
      -- apply
-- refl,


      -- simp,
      -- apply mul_assoc,
    --   simp [alg_equiv.to_alg_hom_eq_coe, prod_ext],-- prod_kronecker_prod₂,
    --     -- ← kronecker_prod₂_assoc],
    --   -- rw kronecker_prod₂_assoc,
    end
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
