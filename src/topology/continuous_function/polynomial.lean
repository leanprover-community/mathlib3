/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.polynomial
import topology.continuous_function.algebra

/-!
# Constructions relating polynomial functions and continuous functions.

This file is just a stub at the moment, but will grow with subsequent PRs
giving abstract statements of the Weierstrass approximation theorem,
and the Stone-Weierstrass theorem.
-/

variables {R : Type*}

namespace polynomial

section
variables [semiring R] [topological_space R] [topological_semiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def to_continuous_map (p : polynomial R) : C(R, R) :=
⟨λ x : R, p.eval x, by continuity⟩

/--
A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def to_continuous_map_on (p : polynomial R) (X : set R) : C(X, R) :=
⟨λ x : X, p.to_continuous_map x, by continuity⟩

-- TODO some lemmas about when `to_continuous_map_on` is injective?

end

section

noncomputable theory

variables [comm_semiring R] [topological_space R] [topological_semiring R]

/--
The algebra map from `polynomial R` to continuous functions `C(R, R)`.
-/
@[simps]
def to_continuous_map_alg_hom : polynomial R →ₐ[R] C(R, R) :=
{ to_fun := λ p, p.to_continuous_map,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := by { intros, ext, simp, },
  commutes' := by { intros, ext, simp [algebra.algebra_map_eq_smul_one], }, }

/--
The algebra map from `polynomial R` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def to_continuous_map_on_alg_hom (X : set R) : polynomial R →ₐ[R] C(X, R)  :=
{ to_fun := λ p, p.to_continuous_map_on X,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := by { intros, ext, simp, },
  commutes' := by { intros, ext, simp [algebra.algebra_map_eq_smul_one], }, }

end

end polynomial

section
variables [comm_semiring R] [topological_space R] [topological_semiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological ring `R`.
-/
def polynomial_functions (X : set R) : subalgebra R C(X, R) :=
(⊤ : subalgebra R (polynomial R)).map (polynomial.to_continuous_map_on_alg_hom X)

@[simp]
lemma polynomial_functions_coe (X : set R) :
  (polynomial_functions X : set C(X, R)) = set.range (polynomial.to_continuous_map_on_alg_hom X) :=
by { ext, simp [polynomial_functions], }

-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces an normed algebra isomorphism between `polynomial_functions X` and
-- `polynomial_functions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.

lemma polynomial_functions_separates_points (X : set R) :
  (polynomial_functions X).separates_points :=
λ x y h,
begin
  -- We use `polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨polynomial.X, ⟨algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩,
  dsimp, simp only [polynomial.eval_X],
  exact (λ h', h (subtype.ext h')),
end

end
