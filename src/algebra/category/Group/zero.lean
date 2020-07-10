/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.shapes.zero

/-!
# The category of commutative additive groups has a zero object.

It also has zero morphisms. For definitional reasons, we infer this from preadditivity rather than
from the existence of a zero object.
-/

open category_theory
open category_theory.limits

universe u

namespace AddCommGroup

instance : has_zero_object AddCommGroup :=
{ zero := 0,
  unique_to := λ X, ⟨⟨0⟩, λ f, begin ext, cases x, erw add_monoid_hom.map_zero, refl end⟩,
  unique_from := λ X, ⟨⟨0⟩, λ f, begin ext, apply subsingleton.elim, end⟩, }

end AddCommGroup
