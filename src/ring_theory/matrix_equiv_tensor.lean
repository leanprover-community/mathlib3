import ring_theory.tensor_product
import data.matrix.basic

universes u v w

open_locale tensor_product
open tensor_product
open algebra.tensor_product

noncomputable theory

variables {R : Type u} [comm_ring R]
variables {A : Type v} [comm_ring A] [algebra R A]
variables {n : Type w} [fintype n] [decidable_eq n]

instance : algebra R (matrix n n A) :=
begin
  change algebra R (algebra.comap R A (matrix n n A)),
  apply_instance,
end

def foo (a : A) (m : matrix n n R) : matrix n n A :=
λ i j, a * algebra_map R A (m i j)

def foo2 (a : A) : matrix n n R →ₗ[R] matrix n n A :=
{ to_fun := foo a, }

def foo3 : A →ₗ[R] matrix n n R →ₗ[R] matrix n n A :=
{ to_fun := foo2, }

def foo4 : A ⊗[R] matrix n n R →ₗ[R] matrix n n A :=
tensor_product.lift foo3

attribute [ext] semimodule distrib_mul_action mul_action has_scalar
#print algebra.to_semimodule
-- FIXME algebra.to_semimodule ≠ matrix.semimodule
def foo5 : (A ⊗[R] matrix n n R) →ₐ[R] matrix n n A :=
alg_hom_of_linear_map_tensor_product
begin
  convert @foo4 R _ A _ _ n _ _,
  ext,
  dsimp [(•)],
  simp,
end
sorry sorry

-- def bar (p : polynomial A) : A ⊗[R] polynomial R :=
-- p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R))

-- def bar2 : polynomial A →ₗ[R] A ⊗[R] polynomial R :=
-- { to_fun := bar, }

-- def bar3 : polynomial A →ₐ[R] A ⊗[R] polynomial R :=
-- { to_fun := bar, }

def matrix_equiv_tensor : matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) :=
sorry
