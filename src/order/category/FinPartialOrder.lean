/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.Fintype
import data.fintype.order
import order.category.PartialOrder

/-!
# The category of finite partial orders

This defines `FinPartialOrder`, the category of finite partial orders.
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

/-- Construct a bundled `FinPartialOrder` from a `fintype` `partial_order`. -/
def of (α : Type*) [partial_order α] [fintype α] : FinPartialOrder := ⟨⟨α⟩⟩

instance : inhabited FinPartialOrder := ⟨of punit⟩

instance : large_category.{u} FinPartialOrder :=
{ hom := λ X Y, order_hom X Y,
  id := λ X, order_hom.id,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, order_hom.comp_id,
  comp_id' := λ X Y, order_hom.id_comp }
--TODO: Missing `order_hom.comp_assoc`

instance : concrete_category FinPartialOrder :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_PartialOrder : has_forget₂ FinPartialOrder PartialOrder :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, id },
  forget_comp := rfl }

instance has_forget_to_Fintype : has_forget₂ FinPartialOrder Fintype :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, coe_fn },
  forget_comp := rfl }

end FinPartialOrder
