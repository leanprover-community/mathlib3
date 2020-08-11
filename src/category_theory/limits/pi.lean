/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.pi.basic
import category_theory.limits.limits
import category_theory.limits.shapes.types

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have chosen limits for each of `F ⋙ pi.eval C i`, we can produce a
   `has_limit F` instance
-/

open category_theory
open category_theory.limits

namespace category_theory.pi

universes v₁ v₂ u₁ u₂

variables {I : Type v₁} {C : I → Type u₁} [∀ i, category.{v₁} (C i)]
variables {J : Type v₁} [small_category J]
variables {F : J ⥤ Π i, C i}

def cone_comp_eval (c : cone F) (i : I) : cone (F ⋙ pi.eval C i) :=
{ X := c.X i,
  π :=
  { app := λ j, c.π.app j i,
    naturality' := λ j j' f, congr_fun (c.π.naturality f) i, } }

def cone_of_cone_comp_eval (c : Π i, cone (F ⋙ pi.eval C i)) : cone F :=
{ X := λ i, (c i).X,
  π :=
  { app := λ j i, (c i).π.app j,
    naturality' := λ j j' f, by { ext i, exact (c i).π.naturality f, } } }

def cone_of_cone_eval_is_limit {c : Π i, cone (F ⋙ pi.eval C i)} (P : Π i, is_limit (c i)) :
  is_limit (cone_of_cone_comp_eval c) :=
{ lift := λ s i, (P i).lift (cone_comp_eval s i),
  fac' := λ s j,
  begin
    ext i,
    exact (P i).fac (cone_comp_eval s i) j,
  end,
  uniq' := λ s m w,
  begin
    ext i,
    exact (P i).uniq (cone_comp_eval s i) (m i) (λ j, congr_fun (w j) i)
  end }

variables [∀ i, has_limit (F ⋙ pi.eval C i)]

def has_limit_of_has_limit_comp_eval : has_limit F :=
{ cone := cone_of_cone_comp_eval (λ i, limit.cone _),
  is_limit := cone_of_cone_eval_is_limit (λ i, limit.is_limit _), }

local attribute [instance] has_limit_of_has_limit_comp_eval

example : has_binary_products (I → Type v₁) := sorry

end category_theory.pi
