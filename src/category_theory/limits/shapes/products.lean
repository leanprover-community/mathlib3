-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.discrete_category

universes v u

open category_theory

namespace category_theory.limits

variables {β : Type v}
variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `functor.of_function`.

abbreviation fan (f : β → C) := cone (functor.of_function f)
abbreviation cofan (f : β → C) := cocone (functor.of_function f)

def fan.mk {f : β → C} {P : C} (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := p } }

def cofan.mk {f : β → C} {P : C} (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := p } }

end category_theory.limits
