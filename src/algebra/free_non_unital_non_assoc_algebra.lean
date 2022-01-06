/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.free
import algebra.monoid_algebra.basic

/-!
# Free algebras

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
@[derive [inhabited, non_unital_non_assoc_semiring]]
def free_non_unital_non_assoc_algebra := monoid_algebra R (free_magma X)

namespace free_non_unital_non_assoc_algebra

variables {X}

/-- The embedding of `X` into the free algebra with coefficients in `R`. -/
def of : X → free_non_unital_non_assoc_algebra R X :=
(monoid_algebra.of_magma R _) ∘ free_magma.of

instance {S : Type*} [monoid S] [distrib_mul_action S R] :
  distrib_mul_action S (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.distrib_mul_action

instance {S₁ S₂ : Type*} [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R] [distrib_mul_action S₂ R]
  [has_scalar S₁ S₂] [is_scalar_tower S₁ S₂ R] :
  is_scalar_tower S₁ S₂ (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.is_scalar_tower

instance {S₁ S₂ : Type*} [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R] [distrib_mul_action S₂ R]
  [smul_comm_class S₁ S₂ R] :
  smul_comm_class S₁ S₂ (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.smul_comm_class

instance {S : Type*} [monoid S] [distrib_mul_action S R] [distrib_mul_action Sᵐᵒᵖ R]
  [is_central_scalar S R] : is_central_scalar S (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.is_central_scalar

instance is_scalar_tower_self {S : Type*} [monoid S] [distrib_mul_action S R]
  [is_scalar_tower S R R] : is_scalar_tower S
    (free_non_unital_non_assoc_algebra R X) (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.is_scalar_tower_self R

instance smul_comm_class_self {S : Type*} [monoid S] [distrib_mul_action S R]
  [smul_comm_class S R R] : smul_comm_class S
    (free_non_unital_non_assoc_algebra R X) (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.smul_comm_class_self R

instance {S : Type*} [semiring S] [module S R] : module S (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.module

instance (R : Type u) [ring R] :
  non_unital_non_assoc_ring (free_non_unital_non_assoc_algebra R X) :=
monoid_algebra.non_unital_non_assoc_ring

variables {A : Type w} [non_unital_non_assoc_semiring A]
variables [module R A] [is_scalar_tower R A A] [smul_comm_class R A A]

/-- The functor `X ↦ free_non_unital_non_assoc_algebra R X` from the category of types to the
category of non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the
other direction. -/
def lift : (X → A) ≃ non_unital_alg_hom R (free_non_unital_non_assoc_algebra R X) A :=
free_magma.lift.trans (monoid_algebra.lift_magma R)

@[simp] lemma lift_symm_apply (F : non_unital_alg_hom R (free_non_unital_non_assoc_algebra R X) A) :
  (lift R).symm F = F ∘ (of R) :=
rfl

@[simp] lemma of_comp_lift (f : X → A) : (lift R f) ∘ (of R) = f :=
(lift R).left_inv f

@[simp] lemma lift_unique
  (f : X → A) (F : non_unital_alg_hom R (free_non_unital_non_assoc_algebra R X) A) :
  F ∘ (of R) = f ↔ F = lift R f :=
(lift R).symm_apply_eq

attribute [irreducible] of lift

@[simp] lemma lift_of_apply (f : X → A) (x) : lift R f (of R x) = f x :=
by rw [← function.comp_app (lift R f) (of R) x, of_comp_lift]

@[simp] lemma lift_comp_of (F : non_unital_alg_hom R (free_non_unital_non_assoc_algebra R X) A) :
  lift R (F ∘ (of R)) = F :=
by rw [← lift_symm_apply, equiv.apply_symm_apply]

@[ext] lemma hom_ext {F₁ F₂ : non_unital_alg_hom R (free_non_unital_non_assoc_algebra R X) A}
  (h : ∀ x, F₁ (of R x) = F₂ (of R x)) : F₁ = F₂ :=
have h' : (lift R).symm F₁ = (lift R).symm F₂, { ext, simp [h], },
(lift R).symm.injective h'

end free_non_unital_non_assoc_algebra
