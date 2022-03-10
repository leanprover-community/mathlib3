/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Frame
import topology.category.Top.basic
import topology.opens

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

universes u

open category_theory opposite order topological_space

/-- The category of locales. -/
@[derive large_category] def Locale := Frameᵒᵖ

namespace Locale

instance : has_coe_to_sort Locale Type* := ⟨λ X, X.unop⟩
instance (X : Locale) : frame X := X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type*) [frame α] : Locale := op $ Frame.of α

@[simp] lemma coe_of (α : Type*) [frame α] : ↥(of α) = α := rfl

instance : inhabited Locale := ⟨of punit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
def Top_to_Locale : Top ⥤ Locale :=
{ obj := λ X, Locale.of (opens X),
  map := λ X Y f, quiver.hom.op (opens.comap f),
  map_id' := λ X, quiver.hom.unop_inj opens.comap_id }
