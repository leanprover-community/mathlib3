-- import ring_theory.tensor_product
-- import data.polynomial

-- universes u v

-- open polynomial
-- open_locale tensor_product
-- open tensor_product
-- open algebra.tensor_product

-- noncomputable theory

-- variables {R : Type u} [comm_ring R]
-- variables {A : Type v} [ring A] [algebra R A]

-- -- FIXME we're missing the `module R (polynomial A)` and `algebra R (polynomial R)` instances.

-- def foo (a : A) (p : polynomial R) : polynomial A :=
-- p.sum (λ n r, monomial n (a * algebra_map R A r))

-- def foo2 (a : A) : polynomial R →ₗ[R] polynomial A :=
-- { to_fun := foo a, }


-- def foo3 : A →ₗ[R] polynomial R →ₗ[R] polynomial A :=
-- { to_fun := foo2, }

-- def foo4 : A ⊗[R] polynomial R →ₗ[R] polynomial A :=
-- tensor_product.lift foo3

-- def foo5 : A ⊗[R] polynomial R →ₐ[R] polynomial A :=
-- alg_hom_of_linear_map_tensor_product foo4 sorry sorry

-- def bar (p : polynomial A) : A ⊗[R] polynomial R :=
-- p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R))

-- def bar2 : polynomial A →ₗ[R] A ⊗[R] polynomial R :=
-- { to_fun := bar, }

-- def bar3 : polynomial A →ₐ[R] A ⊗[R] polynomial R :=
-- { to_fun := bar, }

-- def polynomial_equiv_tensor : polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) :=
-- sorry
