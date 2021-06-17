import linear_algebra.matrix

/-!
# Kronecker product of matrices, see https://en.wikipedia.org/wiki/Kronecker_product

-/


namespace matrix

open_locale tensor_product

variables {α : Type*} [comm_semiring α]
variables {R S T : Type*} [semiring R] [semiring S] [semiring T]
variables [algebra α R] [algebra α S] [algebra α T]
variables {l m n o p q: Type*}
variables [fintype l] [fintype m] [fintype n] [fintype o] [fintype p] [fintype q]

def matrix_tensor_equiv : (matrix l m R) ⊗[α] (matrix n o S) ≃ₗ[α] matrix (l × n) (m × o) (R ⊗[α] S) :=
{ to_fun :=
        begin
          intro A,
          -- λ i j, A i.1 j.1 * f' i.2 j.2
        end,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

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
