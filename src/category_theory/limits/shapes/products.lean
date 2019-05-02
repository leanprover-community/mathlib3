-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes v u

variables {β : Type v}
variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `functor.of_function`.

def fan (f : β → C) := cone (functor.of_function f)

def fan.of_function {f : β → C} {P : C} (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := p } }

def cone.of_fan {β : Type v} {F : (discrete β) ⥤ C} (t : fan (F.obj)) : cone F :=
{ X := t.X,
  π := { app := t.π.app } }

def fan.of_cone {β : Type v} {F : (discrete β) ⥤ C} (t : cone F) : fan (F.obj) :=
{ X := t.X,
  π := { app := t.π.app } }

def fan.π {f : β → C} (t : fan f) (b : β) : t.X ⟶ f b := t.π.app b

def cofan (f : β → C) := cocone (functor.of_function f)

def cofan.of_function {f : β → C} {P : C} (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := p } }

def cocone.of_cofan {β : Type v} {F : (discrete β) ⥤ C} (t : cofan (F.obj)) : cocone F :=
{ X := t.X,
  ι := { app := t.ι.app } }

def cofan.of_cocone {β : Type v} {F : (discrete β) ⥤ C} (t : cocone F) : cofan (F.obj) :=
{ X := t.X,
  ι := { app := t.ι.app } }

def cofan.ι {f : β → C} (t : cofan f) (b : β) : f b ⟶ t.X := t.ι.app b

end category_theory.limits
