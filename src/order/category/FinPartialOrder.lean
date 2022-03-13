/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.Fintype
import order.category.PartialOrder

/-!
# The category of finite partial orders

This defines `FinPartialOrder`, the category of finite partial orders.

Note: `FinPartialOrder` is NOT a subcategory of `BoundedOrder` because its morphisms do not
preserve `⊥` and `⊤`.

## TODO

`FinPartialOrder` is equivalent to a small category.
-/

universes u v

open category_theory

/-- The category of finite partial orders with monotone functions. -/
structure FinPartialOrder :=
(to_PartialOrder : PartialOrder)
[is_fintype : fintype to_PartialOrder]

namespace FinPartialOrder
instance : has_coe_to_sort FinPartialOrder Type* := ⟨λ X, X.to_PartialOrder⟩

instance (X : FinPartialOrder) : partial_order X := X.to_PartialOrder.str

attribute [instance]  FinPartialOrder.is_fintype

/-- Construct a bundled `FinPartialOrder` from `fintype` + `partial_order`. -/
def of (α : Type*) [partial_order α] [fintype α] : FinPartialOrder := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [partial_order α] [fintype α] : ↥(of α) = α := rfl

instance : inhabited FinPartialOrder := ⟨of punit⟩

instance large_category : large_category FinPartialOrder :=
induced_category.category FinPartialOrder.to_PartialOrder

instance concrete_category : concrete_category FinPartialOrder :=
induced_category.concrete_category FinPartialOrder.to_PartialOrder

instance has_forget_to_PartialOrder : has_forget₂ FinPartialOrder PartialOrder :=
induced_category.has_forget₂ FinPartialOrder.to_PartialOrder

instance has_forget_to_Fintype : has_forget₂ FinPartialOrder Fintype :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, coe_fn } }

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : FinPartialOrder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : FinPartialOrder ⥤ FinPartialOrder :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : FinPartialOrder ≌ FinPartialOrder :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinPartialOrder

lemma FinPartialOrder_dual_comp_forget_to_PartialOrder :
  FinPartialOrder.dual ⋙ forget₂ FinPartialOrder PartialOrder =
    forget₂ FinPartialOrder PartialOrder ⋙ PartialOrder.dual := rfl
