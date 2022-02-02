/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.Preorder

/-!
# Category of partial orders

This defines `PartialOrder`, the category of partial orders with monotone maps.
-/

open category_theory

universe u

/-- The category of partially ordered types. -/
def PartialOrder := bundled partial_order

namespace PartialOrder

instance : bundled_hom.parent_projection @partial_order.to_preorder := ⟨⟩

attribute [derive [large_category, concrete_category]] PartialOrder

instance : has_coe_to_sort PartialOrder Type* := bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type*) [partial_order α] : PartialOrder := bundled.of α

instance : inhabited PartialOrder := ⟨of punit⟩

instance (α : PartialOrder) : partial_order α := α.str

instance has_forget_to_Preorder : has_forget₂ PartialOrder Preorder := bundled_hom.forget₂ _ _

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : PartialOrder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def to_dual : PartialOrder ⥤ PartialOrder :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `PartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : PartialOrder ≌ PartialOrder :=
equivalence.mk to_dual to_dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end PartialOrder

lemma PartialOrder_to_dual_comp_forget_to_Preorder :
  PartialOrder.to_dual ⋙ forget₂ PartialOrder Preorder =
    forget₂ PartialOrder Preorder ⋙ Preorder.to_dual := rfl
