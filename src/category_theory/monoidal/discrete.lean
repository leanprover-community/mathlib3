/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.natural_transformation
import category_theory.discrete_category
import algebra.group.hom

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/

universes u

open category_theory

variables (M : Type u) [monoid M]

namespace category_theory

instance monoid_discrete : monoid (discrete M) := by { dsimp [discrete], apply_instance }

instance : monoidal_category (discrete M) :=
{ tensor_unit := 1,
  tensor_obj := λ X Y, X * Y,
  tensor_hom := λ W X Y Z f g, ⟨⟨by rw [f.1.1, g.1.1]⟩⟩,
  left_unitor := λ X, discrete.iso (one_mul X),
  right_unitor := λ X, discrete.iso (mul_one X),
  associator := λ X Y Z, discrete.iso (mul_assoc _ _ _), }

variables {M} {N : Type u} [monoid N]

/--
A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
def discrete.monoidal_functor (F : M →* N) : monoidal_functor (discrete M) (discrete N) :=
{ obj := F,
  map := λ X Y f, ⟨⟨F.congr_arg f.1.1⟩⟩,
  ε := ⟨⟨F.map_one.symm⟩⟩,
  μ := λ X Y, ⟨⟨(F.map_mul X Y).symm⟩⟩, }

variables {K : Type u} [monoid K]

/--
The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
def discrete.monoidal_functor_comp (F : M →* N) (G : N →* K) :
  discrete.monoidal_functor F ⊗⋙ discrete.monoidal_functor G ≅
  discrete.monoidal_functor (G.comp F) :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, }, }

end category_theory
