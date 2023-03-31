/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.Lat

/-!
# Category of linear orders

This defines `LinOrd`, the category of linear orders with monotone maps.
-/

open category_theory

universe u

/-- The category of linear orders. -/
def LinOrd := bundled linear_order

namespace LinOrd

instance : bundled_hom.parent_projection @linear_order.to_partial_order := ⟨⟩

attribute [derive [large_category, concrete_category]] LinOrd

instance : has_coe_to_sort LinOrd Type* := bundled.has_coe_to_sort

/-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
def of (α : Type*) [linear_order α] : LinOrd := bundled.of α

@[simp] lemma coe_of (α : Type*) [linear_order α] : ↥(of α) = α := rfl

instance : inhabited LinOrd := ⟨of punit⟩

instance (α : LinOrd) : linear_order α := α.str

instance has_forget_to_Lat : has_forget₂ LinOrd Lat :=
{ forget₂ := { obj := λ X, Lat.of X,
               map := λ X Y f, (order_hom_class.to_lattice_hom X Y f : lattice_hom X Y) } }

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : LinOrd.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def dual : LinOrd ⥤ LinOrd :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, order_hom.dual }

/-- The equivalence between `LinOrd` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : LinOrd ≌ LinOrd :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end LinOrd

lemma LinOrd_dual_comp_forget_to_Lat :
  LinOrd.dual ⋙ forget₂ LinOrd Lat = forget₂ LinOrd Lat ⋙ Lat.dual :=
rfl
