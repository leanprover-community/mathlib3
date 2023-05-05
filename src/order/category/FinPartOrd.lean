/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.Fintype
import order.category.PartOrd

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is NOT a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/

universes u v

open category_theory

/-- The category of finite partial orders with monotone functions. -/
structure FinPartOrd :=
(to_PartOrd : PartOrd)
[is_fintype : fintype to_PartOrd]

namespace FinPartOrd

instance : has_coe_to_sort FinPartOrd Type* := ⟨λ X, X.to_PartOrd⟩
instance (X : FinPartOrd) : partial_order X := X.to_PartOrd.str
attribute [instance]  FinPartOrd.is_fintype

@[simp] lemma coe_to_PartOrd (X : FinPartOrd) : ↥X.to_PartOrd = ↥X := rfl

/-- Construct a bundled `FinPartOrd` from `fintype` + `partial_order`. -/
def of (α : Type*) [partial_order α] [fintype α] : FinPartOrd := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [partial_order α] [fintype α] : ↥(of α) = α := rfl

instance : inhabited FinPartOrd := ⟨of punit⟩

instance large_category : large_category FinPartOrd :=
induced_category.category FinPartOrd.to_PartOrd

instance concrete_category : concrete_category FinPartOrd :=
induced_category.concrete_category FinPartOrd.to_PartOrd

instance has_forget_to_PartOrd : has_forget₂ FinPartOrd PartOrd :=
induced_category.has_forget₂ FinPartOrd.to_PartOrd

instance has_forget_to_Fintype : has_forget₂ FinPartOrd Fintype :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, coe_fn } }

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : FinPartOrd ⥤ FinPartOrd :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, order_hom.dual }

/-- The equivalence between `FinPartOrd` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : FinPartOrd ≌ FinPartOrd :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinPartOrd

lemma FinPartOrd_dual_comp_forget_to_PartOrd :
  FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl
