/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.cones

open category_theory category_theory.limits

namespace category_theory

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [category.{v₁} C]

section reflects_iso
variables {D : Type u₂} [category.{v₂} D]

/--
Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class reflects_isomorphisms (F : C ⥤ D) :=
(reflects : Π {A B : C} (f : A ⟶ B) [is_iso (F.map f)], is_iso f)

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
def is_iso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D)
  [is_iso (F.map f)] [reflects_isomorphisms F] :
  is_iso f :=
reflects_isomorphisms.reflects F f

end reflects_iso

variables {J : Type v₁} [small_category J] {K : J ⥤ C}

/--
Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
def cone_iso_of_hom_iso {K : J ⥤ C} {c d : cone K} (f : c ⟶ d) [i : is_iso f.hom] :
  is_iso f :=
{ inv :=
  { hom := i.inv,
    w' := λ j, (as_iso f.hom).inv_comp_eq.2 (f.w j).symm } }

/--
Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
def cocone_iso_of_hom_iso {K : J ⥤ C} {c d : cocone K} (f : c ⟶ d) [i : is_iso f.hom] :
  is_iso f :=
{ inv :=
  { hom := i.inv,
    w' := λ j, (as_iso f.hom).comp_inv_eq.2 (f.w j).symm } }

variables {D : Type u₂} [category.{v₁} D]

/--
If `F` reflects isomorphisms, then `cones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
  reflects_isomorphisms (cones.functoriality K F) :=
begin
  constructor,
  introsI,
  haveI : is_iso (F.map f.hom) := (cones.forget (K ⋙ F)).map_is_iso ((cones.functoriality K F).map f),
  haveI := reflects_isomorphisms.reflects F f.hom,
  apply cone_iso_of_hom_iso
end

/--
If `F` reflects isomorphisms, then `cocones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cocone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
  reflects_isomorphisms (cocones.functoriality K F) :=
begin
  constructor,
  introsI,
  haveI : is_iso (F.map f.hom) := (cocones.forget (K ⋙ F)).map_is_iso ((cocones.functoriality K F).map f),
  haveI := reflects_isomorphisms.reflects F f.hom,
  apply cocone_iso_of_hom_iso
end


end category_theory
