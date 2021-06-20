import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product

-/


namespace matrix

open tensor_product
open_locale tensor_product

variables {α : Type*} [comm_semiring α]
variables {R S T : Type*} [semiring R] [semiring S] [semiring T]
variables [algebra α R] [algebra α S] [algebra α T]
variables {l m n o p q: Type*}
variables [fintype l] [fintype m] [fintype n] [fintype o] [fintype p] [fintype q]

def kronecker_bil : (matrix l m R) →ₗ[α] (matrix n o S) →ₗ[α] matrix (l × n) (m × o) (R ⊗[α] S) :=
{ to_fun :=
  begin
    intro A,
    use λ B, λ i j, A i.1 j.1 ⊗ₜ[α] B i.2 j.2,
    all_goals {intros _ _, ext},
    apply tmul_add,
    apply tmul_smul,
  end,
  map_add' := begin
                intros _ _,
                simp only [linear_map.coe_mk, dmatrix.add_apply],
                simp_rw add_tmul,
                refl,
              end,
  map_smul' := begin
                intros a A,
                simp only [pi.smul_apply],
                simp_rw [smul_tmul, tmul_smul],
                refl,
              end, }

def kronecker : (matrix l m R) ⊗[α] (matrix n o S) ≃ₗ[α] matrix (l × n) (m × o) (R ⊗[α] S) :=
{ to_fun := tensor_product.lift kronecker_bil,
  map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
  map_smul' := by simp only [forall_const, eq_self_iff_true, linear_map.map_smul],
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }


-- def matrix_tensor_equiv : (matrix l m R) ⊗[α] (matrix n o S) ≃ₗ[α] matrix (l × n) (m × o) (R ⊗[α] S) :=
-- { to_fun :=
--         begin
--           intro A,
--           -- λ i j, A i.1 j.1 * f' i.2 j.2
--         end,
--   map_add' := sorry,
--   map_smul' := sorry,
--   inv_fun := sorry,
--   left_inv := sorry,
--   right_inv := sorry }

-- def matrix_tensor_equiv_coe : (matrix l m A) ⊗[R] (matrix n o B) →ₗ[R] matrix (l × n) (m × o) (A ⊗[R] B) :=
-- matrix_tensor_equiv

-- def kronecker_prod : (matrix l m A) →ₗ[R] (matrix n o B) →ₗ[R] (matrix (l × n) (m × o) A ⊗[R] B) :=
-- { to_fun := begin
--           intro M,
--           let f : (matrix n o B) →ₗ[R] (matrix (l × n) (m × o) A ⊗[R] B)
--             := λ N : (matrix n o B), (coe : matrix_tensor_equiv _ → _) M ⊗ₜ N,

--           end, --λ M, λ N, matrix_tensor_equiv.to_fun (M ⊗ₜ[R] N),
--   map_add' := _,
--   map_smul' := _ }

-- lemma kronecker :

-- def





end matrix
