/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.limits
import category_theory.discrete_category

universes v u

open category_theory

namespace category_theory.limits

variables {β : Type v}
variables {C : Type u} [𝒞 : category.{v+1} C]
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

/-- `Prod f` computes the product of a family of elements `f`. (It is defined as an abbreviation
   for `limit (functor.of_function f)`, so for most facts about `Prod f`, you will just use general facts
   about limits.) -/
abbreviation Prod (f : β → C) [has_limit (functor.of_function f)] := limit (functor.of_function f)
/-- `Coprod f` computes the coproduct of a family of elements `f`. (It is defined as an abbreviation
   for `colimit (functor.of_function f)`, so for most facts about `Coprod f`, you will just use general facts
   about colimits.) -/
abbreviation Coprod (f : β → C) [has_colimit (functor.of_function f)] := colimit (functor.of_function f)

variables (C)

class has_products :=
(has_limits_of_shape : Π (J : Type v), has_limits_of_shape.{v} (discrete J) C)
class has_coproducts :=
(has_colimits_of_shape : Π (J : Type v), has_colimits_of_shape.{v} (discrete J) C)

attribute [instance] has_products.has_limits_of_shape has_coproducts.has_colimits_of_shape

end category_theory.limits
