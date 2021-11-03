/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.concrete_category.basic
import category_theory.reflects_isomorphisms

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/

universes u

namespace category_theory

instance : reflects_isomorphisms (forget (Type u)) :=
{ reflects := λ X Y f i, i }

variables (C : Type (u+1)) [category C] [concrete_category.{u} C]
variables (D : Type (u+1)) [category D] [concrete_category.{u} D]

/--
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
-- This should not be an instance, as it causes a typeclass loop
-- with `category_theory.has_forget_to_Type`
lemma reflects_isomorphisms_forget₂ [has_forget₂ C D] [reflects_isomorphisms (forget C)] :
  reflects_isomorphisms (forget₂ C D) :=
{ reflects := λ X Y f i,
  begin
    resetI,
    haveI i' : is_iso ((forget D).map ((forget₂ C D).map f)) := functor.map_is_iso (forget D) _,
    haveI : is_iso ((forget C).map f) :=
    begin
      have := has_forget₂.forget_comp,
      dsimp at this,
      rw ←this,
      exact i',
    end,
    apply is_iso_of_reflects_iso f (forget C),
  end }

end category_theory
