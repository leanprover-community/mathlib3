/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import number_theory.modular_forms.jacobi_theta.basic
import analysis.complex.upper_half_plane.manifold

/-!
# Manifold differentiability of the Jacobi's theta function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we reformulate differentiability of the Jacobi's theta function in terms of manifold
differentiability.

## TODO

Prove smoothness (in terms of `smooth`).
-/

open_locale upper_half_plane manifold

lemma mdifferentiable_jacobi_theta : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (jacobi_theta ∘ coe : ℍ → ℂ) :=
λ τ, (differentiable_at_jacobi_theta τ.2).mdifferentiable_at.comp τ τ.mdifferentiable_coe
