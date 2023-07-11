/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Bipointed
import order.category.PartOrd
import order.hom.bounded

/-!
# The category of bounded orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BddOrd`, the category of bounded orders.
-/

universes u v

open category_theory

/-- The category of bounded orders with monotone functions. -/
structure BddOrd :=
(to_PartOrd : PartOrd)
[is_bounded_order : bounded_order to_PartOrd]

namespace BddOrd

instance : has_coe_to_sort BddOrd Type* := induced_category.has_coe_to_sort to_PartOrd
instance (X : BddOrd) : partial_order X := X.to_PartOrd.str

attribute [instance]  BddOrd.is_bounded_order

/-- Construct a bundled `BddOrd` from a `fintype` `partial_order`. -/
def of (α : Type*) [partial_order α] [bounded_order α] : BddOrd := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [partial_order α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BddOrd := ⟨of punit⟩

instance large_category : large_category.{u} BddOrd :=
{ hom := λ X Y, bounded_order_hom X Y,
  id := λ X, bounded_order_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_order_hom.comp_id,
  comp_id' := λ X Y, bounded_order_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_order_hom.comp_assoc _ _ _ }

instance concrete_category : concrete_category BddOrd :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_PartOrd : has_forget₂ BddOrd PartOrd :=
{ forget₂ := { obj := λ X, X.to_PartOrd, map := λ X Y, bounded_order_hom.to_order_hom } }

instance has_forget_to_Bipointed : has_forget₂ BddOrd Bipointed :=
{ forget₂ := { obj := λ X, ⟨X, ⊥, ⊤⟩, map := λ X Y f, ⟨f, map_bot f, map_top f⟩ },
  forget_comp := rfl }

/-- `order_dual` as a functor. -/
@[simps] def dual : BddOrd ⥤ BddOrd :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_order_hom.dual }

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : BddOrd.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- The equivalence between `BddOrd` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BddOrd ≌ BddOrd :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BddOrd

lemma BddOrd_dual_comp_forget_to_PartOrd :
  BddOrd.dual ⋙ forget₂ BddOrd PartOrd =
    forget₂ BddOrd PartOrd ⋙ PartOrd.dual := rfl

lemma BddOrd_dual_comp_forget_to_Bipointed :
  BddOrd.dual ⋙ forget₂ BddOrd Bipointed =
    forget₂ BddOrd Bipointed ⋙ Bipointed.swap := rfl
