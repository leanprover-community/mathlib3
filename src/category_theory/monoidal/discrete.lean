/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.hom.group
import category_theory.discrete_category
import category_theory.monoidal.natural_transformation

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/

universes u

open category_theory
open category_theory.discrete

variables (M : Type u) [monoid M]

namespace category_theory

@[to_additive discrete.add_monoidal, simps tensor_obj_as tensor_unit_as]
instance discrete.monoidal : monoidal_category (discrete M) :=
{ tensor_unit := discrete.mk 1,
  tensor_obj := λ X Y, discrete.mk (X.as * Y.as),
  tensor_hom := λ W X Y Z f g, eq_to_hom (by rw [eq_of_hom f, eq_of_hom g]),
  left_unitor := λ X, discrete.eq_to_iso (one_mul X.as),
  right_unitor := λ X, discrete.eq_to_iso (mul_one X.as),
  associator := λ X Y Z, discrete.eq_to_iso (mul_assoc _ _ _ ), }

variables {M} {N : Type u} [monoid N]

/--
A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive discrete.add_monoidal_functor "An additive morphism between add_monoids gives a
  monoidal functor between the corresponding discrete monoidal categories.", simps]
def discrete.monoidal_functor (F : M →* N) : monoidal_functor (discrete M) (discrete N) :=
{ obj := λ X, discrete.mk (F X.as),
  map := λ X Y f, discrete.eq_to_hom (F.congr_arg (eq_of_hom f)),
  ε := discrete.eq_to_hom F.map_one.symm,
  μ := λ X Y, discrete.eq_to_hom (F.map_mul X.as Y.as).symm, }

variables {K : Type u} [monoid K]

/--
The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive discrete.add_monoidal_functor_comp "The monoidal natural isomorphism corresponding to
composing two additive morphisms."]
def discrete.monoidal_functor_comp (F : M →* N) (G : N →* K) :
  discrete.monoidal_functor F ⊗⋙ discrete.monoidal_functor G ≅
  discrete.monoidal_functor (G.comp F) :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, }, }

end category_theory
