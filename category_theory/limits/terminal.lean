-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.limits.products
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def is_terminal (X : C) := is_limit ({ X := X, π := { app := pempty.rec _ } } : cone (functor.empty C))
def is_initial (X : C) := is_colimit ({ X := X, ι := { app := pempty.rec _ } } : cocone (functor.empty C))

variables {X : C}

instance is_terminal_subsingleton : subsingleton (is_terminal X) := by dsimp [is_terminal]; apply_instance
instance is_initial_subsingleton : subsingleton (is_initial X) := by dsimp [is_initial]; apply_instance

variable (C)

class has_terminal :=
(terminal : C)
(is_terminal : is_terminal terminal . obviously)
class has_initial :=
(initial : C)
(is_initial : is_initial initial . obviously)

def terminal_object [has_terminal.{u v} C] := has_terminal.terminal
def initial_object [has_initial.{u v} C] := has_initial.initial

-- Special cases of this may be marked with [instance] as desired.
def has_terminal_of_has_limits [limits.has_limits.{u v} C] : has_terminal.{u v} C :=
{ terminal := limit (functor.empty C),
  is_terminal := is_limit_invariance _ _ (by tidy) (limit.universal_property (functor.empty C)) }
def has_initial_of_has_colimits [limits.has_colimits.{u v} C] : has_initial.{u v} C :=
{ initial := colimit (functor.empty C),
  is_initial := is_colimit_invariance _ _ (by tidy) (colimit.universal_property (functor.empty C)) }

def has_terminal_of_has_products [has_products.{u v} C] : has_terminal.{u v} C :=
{ terminal := limits.pi (pempty.rec _),
  is_terminal := begin tidy, apply pi.lift, tidy, end }
def has_initial_of_has_coproducts [has_coproducts.{u v} C] : has_initial.{u v} C :=
{ initial := limits.sigma (pempty.rec _),
  is_initial := begin tidy, apply sigma.desc, tidy, end }

end category_theory.limits
