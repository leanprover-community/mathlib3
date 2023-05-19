/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.braided
import category_theory.monoidal.of_chosen_finite_products.basic

/-!
# The symmetric monoidal structure on a category with chosen finite products.

-/

universes v u

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {X Y : C}

open category_theory.limits

section
local attribute [tidy] tactic.case_bash

variables {C}
variables (𝒯 : limit_cone (functor.empty.{v} C))
variables (ℬ : Π (X Y : C), limit_cone (pair X Y))

open monoidal_of_chosen_finite_products

namespace monoidal_of_chosen_finite_products

open monoidal_category

lemma braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
  (tensor_hom ℬ f g) ≫ (limits.binary_fan.braiding (ℬ Y Y').is_limit (ℬ Y' Y).is_limit).hom =
    (limits.binary_fan.braiding (ℬ X X').is_limit (ℬ X' X).is_limit).hom ≫ (tensor_hom ℬ g f) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

lemma hexagon_forward (X Y Z : C) :
  (binary_fan.associator_of_limit_cone ℬ X Y Z).hom ≫
    (limits.binary_fan.braiding
      (ℬ X (tensor_obj ℬ Y Z)).is_limit
      (ℬ (tensor_obj ℬ Y Z) X).is_limit).hom ≫
    (binary_fan.associator_of_limit_cone ℬ Y Z X).hom =
    (tensor_hom ℬ (limits.binary_fan.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom (𝟙 Z)) ≫
      (binary_fan.associator_of_limit_cone ℬ Y X Z).hom ≫
        (tensor_hom ℬ (𝟙 Y) (limits.binary_fan.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩,
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩;
    { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, }, }
end

lemma hexagon_reverse (X Y Z : C) :
  (binary_fan.associator_of_limit_cone ℬ X Y Z).inv ≫
    (limits.binary_fan.braiding
      (ℬ (tensor_obj ℬ X Y) Z).is_limit
      (ℬ Z (tensor_obj ℬ X Y)).is_limit).hom ≫
    (binary_fan.associator_of_limit_cone ℬ Z X Y).inv =
    (tensor_hom ℬ (𝟙 X) (limits.binary_fan.braiding (ℬ Y Z).is_limit (ℬ Z Y).is_limit).hom) ≫
      (binary_fan.associator_of_limit_cone ℬ X Z Y).inv ≫
        (tensor_hom ℬ (limits.binary_fan.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom (𝟙 Y)) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩,
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩;
    { dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
        limits.is_limit.cone_point_unique_up_to_iso],
      simp, }, },
  { dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
      limits.is_limit.cone_point_unique_up_to_iso],
    simp, },
end

lemma symmetry (X Y : C) :
  (limits.binary_fan.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom ≫
      (limits.binary_fan.braiding (ℬ Y X).is_limit (ℬ X Y).is_limit).hom =
    𝟙 (tensor_obj ℬ X Y) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟨⟩⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

end monoidal_of_chosen_finite_products

open monoidal_of_chosen_finite_products

/--
The monoidal structure coming from finite products is symmetric.
-/
def symmetric_of_chosen_finite_products :
  symmetric_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
{ braiding := λ X Y, limits.binary_fan.braiding (ℬ _ _).is_limit (ℬ _ _).is_limit,
  braiding_naturality' := λ X X' Y Y' f g, braiding_naturality ℬ f g,
  hexagon_forward' := λ X Y Z, hexagon_forward ℬ X Y Z,
  hexagon_reverse' := λ X Y Z, hexagon_reverse ℬ X Y Z,
  symmetry' := λ X Y, symmetry ℬ X Y, }

end

end category_theory
