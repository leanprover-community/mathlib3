/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BddDistLat
import order.heyting.hom

/-!
# The category of Heyting algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `HeytAlg`, the category of Heyting algebras.
-/

universes u

open category_theory opposite order

/-- The category of Heyting algebras. -/
def HeytAlg := bundled heyting_algebra

namespace HeytAlg

instance : has_coe_to_sort HeytAlg Type* := bundled.has_coe_to_sort
instance (X : HeytAlg) : heyting_algebra X := X.str

/-- Construct a bundled `HeytAlg` from a `heyting_algebra`. -/
def of (α : Type*) [heyting_algebra α] : HeytAlg := bundled.of α

@[simp] lemma coe_of (α : Type*) [heyting_algebra α] : ↥(of α) = α := rfl

instance : inhabited HeytAlg := ⟨of punit⟩

instance bundled_hom : bundled_hom heyting_hom :=
{ to_fun := λ α β [heyting_algebra α] [heyting_algebra β],
    by exactI (coe_fn : heyting_hom α β → α → β),
  id := heyting_hom.id,
  comp := @heyting_hom.comp,
  hom_ext := λ α β [heyting_algebra α] [heyting_algebra β], by exactI fun_like.coe_injective }

attribute [derive [large_category, concrete_category]] HeytAlg

@[simps]
instance has_forget_to_Lat : has_forget₂ HeytAlg BddDistLat :=
{ forget₂ := { obj := λ X, BddDistLat.of X,
               map := λ X Y f, (f : bounded_lattice_hom X Y) } }

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps] def iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end HeytAlg
