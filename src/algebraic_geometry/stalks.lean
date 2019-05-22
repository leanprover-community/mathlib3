-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import algebraic_geometry.presheafed_space
import category_theory.instances.Top.stalks

universes v u v' u'

open category_theory
open category_theory.instances
open category_theory.limits
open algebraic_geometry
open topological_space

variables {C : Type u} [𝒞 : category.{v+1} C] [has_colimits.{v} C]
include 𝒞

open category_theory.instances.Top.presheaf

namespace algebraic_geometry.PresheafedSpace

def stalk (X : PresheafedSpace.{v} C) (x : X) : C := X.𝒪.stalk x

def stalk_map {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) (x : X) : Y.stalk (α x) ⟶ X.stalk x :=
(stalk_functor C (α x)).map (α.c) ≫ X.𝒪.stalk_pushforward C α x

namespace stalk_map

@[simp] lemma id (X : PresheafedSpace.{v} C) (x : X) : stalk_map (𝟙 X) x = 𝟙 (X.stalk x) :=
begin
  dsimp [stalk_map],
  simp only [stalk_pushforward.id],
  rw [←category_theory.functor.map_comp],
  convert (stalk_functor C x).map_id X.𝒪,
  ext U,
  op_induction U,
  cases U,
  dsimp,
  simp only [pushforward.id_hom_app],
  dsimp,
  simp,
end
.

@[simp] lemma comp {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
  stalk_map (α ≫ β) x =
    (stalk_map β (α x) : Z.stalk (β (α x)) ⟶ Y.stalk (α x)) ≫
    (stalk_map α x : Y.stalk (α x) ⟶ X.stalk x) :=
begin
  dsimp [stalk, stalk_map, stalk_functor, stalk_pushforward, comp_c],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colim.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre,
    whisker_left.app, whisker_right.app,
    functor.map_comp, category.assoc, category_theory.functor.map_id, category.id_comp],
  dsimp,
  simp only [category_theory.functor.map_id],
  erw [category.id_comp, category.id_comp],
end
end stalk_map

end algebraic_geometry.PresheafedSpace
