/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.punit
import category_theory.limits.has_limits

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples,
we show all (co)cones into `discrete punit` are (co)limit (co)cones,
and `discrete punit` has all (co)limits.
-/

universe v

open category_theory
namespace category_theory.limits


variables {J : Type v} [small_category J] {F : J ⥤ discrete punit.{v+1}}

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


end category_theory.limits
