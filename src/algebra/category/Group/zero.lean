/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.shapes.zero

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

open category_theory
open category_theory.limits

universe u

namespace Group

@[to_additive AddGroup.has_zero_object]
instance : has_zero_object Group :=
{ zero := 1,
  unique_to := λ X, ⟨⟨1⟩, λ f, by { ext, cases x, erw monoid_hom.map_one, refl, }⟩,
  unique_from := λ X, ⟨⟨1⟩, λ f, by ext⟩, }

end Group

namespace CommGroup

@[to_additive AddCommGroup.has_zero_object]
instance : has_zero_object CommGroup :=
{ zero := 1,
  unique_to := λ X, ⟨⟨1⟩, λ f, by { ext, cases x, erw monoid_hom.map_one, refl, }⟩,
  unique_from := λ X, ⟨⟨1⟩, λ f, by ext⟩, }

end CommGroup
