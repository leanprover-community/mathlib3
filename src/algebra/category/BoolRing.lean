/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.category.Ring.basic
import algebra.ring.boolean_ring
import order.category.BoolAlg

/-!
# The category of Boolean rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/

universes u

open category_theory order

/-- The category of Boolean rings. -/
def BoolRing := bundled boolean_ring

namespace BoolRing

instance : has_coe_to_sort BoolRing Type* := bundled.has_coe_to_sort
instance (X : BoolRing) : boolean_ring X := X.str

/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type*) [boolean_ring α] : BoolRing := bundled.of α

@[simp] lemma coe_of (α : Type*) [boolean_ring α] : ↥(of α) = α := rfl

instance : inhabited BoolRing := ⟨of punit⟩

instance : bundled_hom.parent_projection @boolean_ring.to_comm_ring := ⟨⟩

attribute [derive [large_category, concrete_category]] BoolRing

@[simps] instance has_forget_to_CommRing : has_forget₂ BoolRing CommRing := bundled_hom.forget₂ _ _

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps] def iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

@[simps] instance BoolRing.has_forget_to_BoolAlg : has_forget₂ BoolRing BoolAlg :=
{ forget₂ := { obj := λ X, BoolAlg.of (as_boolalg X), map := λ X Y, ring_hom.as_boolalg } }

@[simps] instance BoolAlg.has_forget_to_BoolRing : has_forget₂ BoolAlg BoolRing :=
{ forget₂ := { obj := λ X, BoolRing.of (as_boolring X),
               map := λ X Y, bounded_lattice_hom.as_boolring } }

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse] def BoolRing_equiv_BoolAlg : BoolRing ≌ BoolAlg :=
equivalence.mk (forget₂ BoolRing BoolAlg) (forget₂ BoolAlg BoolRing)
  (nat_iso.of_components (λ X, BoolRing.iso.mk $ (ring_equiv.as_boolring_as_boolalg X).symm) $
    λ X Y f, rfl)
  (nat_iso.of_components (λ X, BoolAlg.iso.mk $ order_iso.as_boolalg_as_boolring X) $
    λ X Y f, rfl)
