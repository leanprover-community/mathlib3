/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.concrete_category.bundled_hom
import topology.bornology.hom

/-!
# The category of bornological spaces

This defines `Born`, the category of bornological spaces.

## TODO

The free functor from `Born` to `BoundedBorn` is `X → with_top (with_bot X)`.
-/

universes u

open category_theory

/-- The category of bornological_spaces. -/
def Born := bundled bornological_space

namespace Born

instance : has_coe_to_sort Born Type* := bundled.has_coe_to_sort
instance (X : Born) : bornological_space X := X.str

/-- Construct a bundled `Born` from a `bornological_space`. -/
def of (α : Type*) [bornological_space α] : Born := bundled.of α

instance : inhabited Born := ⟨of punit⟩

instance : bundled_hom @bounded_map :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @bounded_map.id,
  comp := @bounded_map.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }

instance : large_category.{u} Born := bundled_hom.category bounded_map
instance : concrete_category Born := bundled_hom.concrete_category bounded_map

end Born
