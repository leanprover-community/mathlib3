/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import topology.sheaves.sheaf_condition.sites
import category_theory.sites.limits
import category_theory.limits.functor_category

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

variables {C : Type u} [category.{v} C]

namespace Top

instance [has_limits C] (X : Top) : has_limits (presheaf C X) :=
by { dsimp [presheaf], apply_instance, }

instance [has_colimits C] (X : Top) : has_colimits (presheaf C X) :=
by { dsimp [presheaf], apply_instance, }

instance [has_limits C] (X : Top) : has_limits (sheaf C X) :=
by { apply adjunction.as_limits_of_equivalence, }

end Top
