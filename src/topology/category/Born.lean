/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.concrete_category.bundled_hom
import topology.bornology.hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/

universes u

open category_theory

/-- The category of bornologies. -/
def Born := bundled bornology

namespace Born

instance : has_coe_to_sort Born Type* := bundled.has_coe_to_sort
instance (X : Born) : bornology X := X.str

/-- Construct a bundled `Born` from a `bornology`. -/
def of (α : Type*) [bornology α] : Born := bundled.of α

instance : inhabited Born := ⟨of punit⟩

instance : bundled_hom @locally_bounded_map :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @locally_bounded_map.id,
  comp := @locally_bounded_map.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }

instance : large_category.{u} Born := bundled_hom.category locally_bounded_map
instance : concrete_category Born := bundled_hom.concrete_category locally_bounded_map

end Born
