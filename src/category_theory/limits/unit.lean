/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.punit
import category_theory.limits.has_limits

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `discrete punit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `discrete punit` has all
(co)limits.
-/

universes v u

open category_theory
namespace category_theory.limits

section punit_has_limits
variables {J : Type v} [small_category J] {F : J ⥤ discrete punit}

/-- A trivial cone for a functor into `punit`. `punit_cone_is_limit` shows it is a limit. -/
def punit_cone : cone F :=
⟨⟨⟨⟩⟩, (functor.punit_ext _ _).hom⟩

/-- A trivial cocone for a functor into `punit`. `punit_cocone_is_limit` shows it is a colimit. -/
def punit_cocone : cocone F :=
⟨⟨⟨⟩⟩, (functor.punit_ext _ _).hom⟩

/--
Any cone over a functor into `punit` is a limit cone.
-/
def punit_cone_is_limit {c : cone F} : is_limit c :=
by tidy

/--
Any cocone over a functor into `punit` is a colimit cocone.
-/
def punit_cocone_is_colimit {c : cocone F} : is_colimit c :=
by tidy

instance : has_limits (discrete punit) :=
by tidy

instance : has_colimits (discrete punit) :=
by tidy

end punit_has_limits

section shape_punit
variables {C : Type u} [category.{v} C] (F : discrete punit ⥤ C)

@[simps]
def punit_cone' : cone F :=
{ X := F.obj ⟨punit.star⟩,
  π :=
  { app := λ u, F.map ⟨⟨dec_trivial⟩⟩,
    naturality' := λ X Y f,
    begin
      dsimp,
      simp,
      rw [←F.map_comp],
      congr,
    end } }

def punit_cone'_is_limit : is_limit (punit_cone' F) :=
{ lift := λ s, s.π.app ⟨punit.star⟩,
  fac' := λ s j, by simp only [punit_cone'_π_app, cone.w],
  uniq' := λ s m h, by { convert h ⟨punit.star⟩, tidy } }

@[simps]
def punit_cocone' : cocone F :=
{ X := F.obj ⟨punit.star⟩,
  ι :=
  { app := λ u, F.map ⟨⟨dec_trivial⟩⟩,
    naturality' := λ X Y f,
    begin
      dsimp,
      simp,
      rw [←F.map_comp],
      congr,
    end } }

def punit_cocone'_is_colimit : is_colimit (punit_cocone' F) :=
{ desc := λ s, s.ι.app ⟨punit.star⟩,
  fac' := λ s j, by simp only [punit_cocone'_ι_app, cocone.w],
  uniq' := λ s m h, by { convert h ⟨punit.star⟩, tidy } }


end shape_punit


end category_theory.limits
