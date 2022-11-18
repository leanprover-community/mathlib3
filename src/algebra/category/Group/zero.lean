/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.shapes.zero_objects

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

open category_theory
open category_theory.limits

universe u

namespace Group

@[to_additive] lemma is_zero_of_subsingleton (G : Group) [subsingleton G] :
  is_zero G :=
begin
  refine ⟨λ X, ⟨⟨⟨1⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨1⟩, λ f, _⟩⟩⟩,
  { ext, have : x = 1 := subsingleton.elim _ _, rw [this, map_one, map_one], },
  { ext, apply subsingleton.elim }
end

@[to_additive AddGroup.has_zero_object]
instance : has_zero_object Group :=
⟨⟨of punit, is_zero_of_subsingleton _⟩⟩

end Group

namespace CommGroup

@[to_additive] lemma is_zero_of_subsingleton (G : CommGroup) [subsingleton G] :
  is_zero G :=
begin
  refine ⟨λ X, ⟨⟨⟨1⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨1⟩, λ f, _⟩⟩⟩,
  { ext, have : x = 1 := subsingleton.elim _ _, rw [this, map_one, map_one], },
  { ext, apply subsingleton.elim }
end

@[to_additive AddCommGroup.has_zero_object]
instance : has_zero_object CommGroup :=
⟨⟨of punit, is_zero_of_subsingleton _⟩⟩

end CommGroup
