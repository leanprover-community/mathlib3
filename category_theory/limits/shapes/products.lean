-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes u v w

variables {β : Type v}
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def fan (f : β → C) := cone (functor.of_function f)

@[simp] def fan.of_function
  {f : β → C} {P : C} (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := p } }

def cone.of_fan {β : Type v} {F : (discrete β) ⥤ C} (t : fan (F.obj)) : cone F :=
{ X := t.X,
  π := { app := t.π.app } }

def fan.of_cone {β : Type v} {F : (discrete β) ⥤ C} (t : cone F) : fan (F.obj) :=
{ X := t.X,
  π := { app := t.π.app } }

def cofan (f : β → C) := cocone (functor.of_function f)

@[simp] def cofan.of_function
  {f : β → C} {P : C} (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := p } }

def cocone.of_cofan {β : Type v} {F : (discrete β) ⥤ C} (t : cofan (F.obj)) : cocone F :=
{ X := t.X,
  ι := { app := t.ι.app } }

def cofan.of_cocone {β : Type v} {F : (discrete β) ⥤ C} (t : cocone F) : cofan (F.obj) :=
{ X := t.X,
  ι := { app := t.ι.app } }

end category_theory.limits
