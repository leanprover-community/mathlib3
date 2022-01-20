/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
import data.equiv.module
import data.real.basic

/-!
# Test file for conjugate linear maps

The implementation of conjugate-linear maps in mathlib is designed to have a few convenient
properties:

1. A conjugate-linear map with respect to the ring `ℝ` (or any other ring given the "trivial"
  `star_ring` instance) is *definitionally* a plain linear map; that is, the type is the same.

2. The composition of two conjugate-linear maps is *definitionally* a plain linear map.

3. The composition of a plain linear map and a conjugate-linear map is conjugate-linear.

4. The inverse of a conjugate-linear equivalence is *definitionally* a conjugate-linear
  equivalence.

This file contains tests to make sure that future refactors do not lose these definitional
properties.

## Tags

Conjugate linear maps, semilinear maps

-/

section real
variables {M : Type*} [add_comm_monoid M] [module ℝ M]
variables {M₂ : Type*} [add_comm_monoid M₂] [module ℝ M₂]

example (f : M →ₗ⋆[ℝ] M₂) : M →ₗ[ℝ] M₂ := f

example (f : M →ₗ[ℝ] M₂) : M →ₗ⋆[ℝ] M₂ := f

end real

section star_ring
variables {R : Type*} [comm_semiring R] [star_ring R]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {M₂ : Type*} [add_comm_monoid M₂] [module R M₂]
variables {M₃ : Type*} [add_comm_monoid M₃] [module R M₃]

example (f : M →ₗ⋆[R] M₂) (g : M₂ →ₗ⋆[R] M₃) : M →ₗ[R] M₃ := g.comp f

example (f : M →ₗ[R] M₂) (g : M₂ →ₗ⋆[R] M₃) : M →ₗ⋆[R] M₃ := g.comp f
example (f : M →ₗ⋆[R] M₂) (g : M₂ →ₗ[R] M₃) : M →ₗ⋆[R] M₃ := g.comp f

example (f : M ≃ₗ⋆[R] M₂) : M₂ ≃ₗ⋆[R] M := f.symm

end star_ring
