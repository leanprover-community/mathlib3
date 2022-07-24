/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Bipointed
import order.category.PartialOrder
import order.hom.bounded

/-!
# The category of bounded orders

This defines `BoundedOrder`, the category of bounded orders.
-/

universes u v

open category_theory

/-- The category of bounded orders with monotone functions. -/
structure BoundedOrder :=
(to_PartialOrder : PartialOrder)
[is_bounded_order : bounded_order to_PartialOrder]

namespace BoundedOrder

instance : has_coe_to_sort BoundedOrder Type* := induced_category.has_coe_to_sort to_PartialOrder
instance (X : BoundedOrder) : partial_order X := X.to_PartialOrder.str

attribute [instance]  BoundedOrder.is_bounded_order

/-- Construct a bundled `BoundedOrder` from a `fintype` `partial_order`. -/
def of (α : Type*) [partial_order α] [bounded_order α] : BoundedOrder := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [partial_order α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BoundedOrder := ⟨of punit⟩

instance large_category : large_category.{u} BoundedOrder :=
{ hom := λ X Y, bounded_order_hom X Y,
  id := λ X, bounded_order_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_order_hom.comp_id,
  comp_id' := λ X Y, bounded_order_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_order_hom.comp_assoc _ _ _ }

instance concrete_category : concrete_category BoundedOrder :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_PartialOrder : has_forget₂ BoundedOrder PartialOrder :=
{ forget₂ := { obj := λ X, X.to_PartialOrder, map := λ X Y, bounded_order_hom.to_order_hom } }

instance has_forget_to_Bipointed : has_forget₂ BoundedOrder Bipointed :=
{ forget₂ := { obj := λ X, ⟨X, ⊥, ⊤⟩, map := λ X Y f, ⟨f, map_bot f, map_top f⟩ },
  forget_comp := rfl }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoundedOrder ⥤ BoundedOrder :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_order_hom.dual }

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : BoundedOrder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- The equivalence between `BoundedOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoundedOrder ≌ BoundedOrder :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoundedOrder

lemma BoundedOrder_dual_comp_forget_to_PartialOrder :
  BoundedOrder.dual ⋙ forget₂ BoundedOrder PartialOrder =
    forget₂ BoundedOrder PartialOrder ⋙ PartialOrder.dual := rfl

lemma BoundedOrder_dual_comp_forget_to_Bipointed :
  BoundedOrder.dual ⋙ forget₂ BoundedOrder Bipointed =
    forget₂ BoundedOrder Bipointed ⋙ Bipointed.swap := rfl
