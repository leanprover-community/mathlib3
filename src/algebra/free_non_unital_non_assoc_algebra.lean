/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.free
import algebra.monoid_algebra.basic

/-!
# Free algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a semiring `R` and a type `X`, we construct the free non-unital, non-associative algebra on
`X` with coefficients in `R`, together with its universal property. The construction is valuable
because it can be used to build free algebras with more structure, e.g., free Lie algebras.

Note that elsewhere we have a construction of the free unital, associative algebra. This is called
`free_algebra`.

## Main definitions

  * `free_non_unital_non_assoc_algebra`
  * `free_non_unital_non_assoc_algebra.lift`
  * `free_non_unital_non_assoc_algebra.of`

## Implementation details

We construct the free algebra as the magma algebra, with coefficients in `R`, of the free magma on
`X`. However we regard this as an implementation detail and thus deliberately omit the lemmas
`of_apply` and `lift_apply`, and we mark `free_non_unital_non_assoc_algebra` and `lift` as
irreducible once we have established the universal property.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/

universes u v w

noncomputable theory

variables (R : Type u) (X : Type v) [semiring R]

/-- The free non-unital, non-associative algebra on the type `X` with coefficients in `R`. -/
abbreviation free_non_unital_non_assoc_algebra := monoid_algebra R (free_magma X)

namespace free_non_unital_non_assoc_algebra

variables {X}

/-- The embedding of `X` into the free algebra with coefficients in `R`. -/
def of : X → free_non_unital_non_assoc_algebra R X :=
(monoid_algebra.of_magma R _) ∘ free_magma.of

variables {A : Type w} [non_unital_non_assoc_semiring A]
variables [module R A] [is_scalar_tower R A A] [smul_comm_class R A A]

/-- The functor `X ↦ free_non_unital_non_assoc_algebra R X` from the category of types to the
category of non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the
other direction. -/
def lift : (X → A) ≃ (free_non_unital_non_assoc_algebra R X →ₙₐ[R] A) :=
free_magma.lift.trans (monoid_algebra.lift_magma R)

@[simp] lemma lift_symm_apply (F : free_non_unital_non_assoc_algebra R X →ₙₐ[R] A) :
  (lift R).symm F = F ∘ (of R) :=
rfl

@[simp] lemma of_comp_lift (f : X → A) : (lift R f) ∘ (of R) = f :=
(lift R).left_inv f

@[simp] lemma lift_unique
  (f : X → A) (F : free_non_unital_non_assoc_algebra R X →ₙₐ[R] A) :
  F ∘ (of R) = f ↔ F = lift R f :=
(lift R).symm_apply_eq

@[simp] lemma lift_of_apply (f : X → A) (x) : lift R f (of R x) = f x :=
congr_fun (of_comp_lift _ f) x

@[simp] lemma lift_comp_of (F : free_non_unital_non_assoc_algebra R X →ₙₐ[R] A) :
  lift R (F ∘ (of R)) = F :=
(lift R).apply_symm_apply F

@[ext] lemma hom_ext {F₁ F₂ : free_non_unital_non_assoc_algebra R X →ₙₐ[R] A}
  (h : ∀ x, F₁ (of R x) = F₂ (of R x)) : F₁ = F₂ :=
(lift R).symm.injective $ funext h

end free_non_unital_non_assoc_algebra
