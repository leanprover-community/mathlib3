/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.preserves.finite

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.#check

## Implementation notes

Due to the way preservation of finite limits is defined, we currently only define these categories
when the morphisms of the source and target category live in the same unvierse.

-/

universes v u₁ u₂

open category_theory.limits

namespace category_theory
variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

section
variables (C) (D)

/-- Bundled left-exact functors -/
@[derive category]
def LeftExactFunctor :=
{ F : C ⥤ D // nonempty (preserves_finite_limits F) }

infixr ` ⥤ₗ `:26 := LeftExactFunctor

/-- Bundled right-exact functors -/
@[derive category]
def RightExactFunctor :=
{ F : C ⥤ D // nonempty (preserves_finite_colimits F) }

infixr ` ⥤ᵣ `:26 := RightExactFunctor

/-- Bundled exact functors -/
@[derive category]
def ExactFunctor :=
{ F : C ⥤ D // nonempty (preserves_finite_limits F) ∧ nonempty (preserves_finite_colimits F) }

infixr ` ⥤ₑ `:26 := ExactFunctor

@[simps]
def LeftExact.of_exact : (C ⥤ₑ D) ⥤ (C ⥤ₗ D) :=
{ obj := λ F, ⟨F.1, F.2.1⟩,
  map := λ X Y f, f }

@[simps]
def RightExact.of_exact : (C ⥤ₑ D) ⥤ (C ⥤ᵣ D) :=
{ obj := λ F, ⟨F.1, F.2.2⟩,
  map := λ X Y f, f }



end

end category_theory
