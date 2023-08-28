/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.PartOrd
import order.hom.lattice

/-!
# The categories of semilattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `SemilatSup` and `SemilatInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/

universes u
open category_theory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatSup : Type.{u+1} :=
(X : Type.{u})
[is_semilattice_sup : semilattice_sup X]
[is_order_bot : order_bot X]

/-- The category of inf-semilattices with a top element. -/
structure SemilatInf : Type.{u+1} :=
(X : Type.{u})
[is_semilattice_inf : semilattice_inf X]
[is_order_top : order_top X]

attribute [protected] SemilatSup.X SemilatInf.X

namespace SemilatSup

instance : has_coe_to_sort SemilatSup Type* := ⟨SemilatSup.X⟩
attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatSup` from a `semilattice_sup`. -/
def of (α : Type*) [semilattice_sup α] [order_bot α] : SemilatSup := ⟨α⟩

@[simp] lemma coe_of (α : Type*) [semilattice_sup α] [order_bot α] : ↥(of α) = α := rfl

instance : inhabited SemilatSup := ⟨of punit⟩

instance : large_category.{u} SemilatSup :=
{ hom := λ X Y, sup_bot_hom X Y,
  id := λ X, sup_bot_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, sup_bot_hom.comp_id,
  comp_id' := λ X Y, sup_bot_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, sup_bot_hom.comp_assoc _ _ _ }

instance : concrete_category SemilatSup :=
{ forget := { obj := SemilatSup.X, map := λ X Y, coe_fn },
  forget_faithful := ⟨λ X Y, fun_like.coe_injective⟩ }

instance has_forget_to_PartOrd : has_forget₂ SemilatSup PartOrd :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f } }

@[simp] lemma coe_forget_to_PartOrd (X : SemilatSup) :
  ↥((forget₂ SemilatSup PartOrd).obj X) = ↥X := rfl

end SemilatSup

namespace SemilatInf

instance : has_coe_to_sort SemilatInf Type* := ⟨SemilatInf.X⟩

attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatInf` from a `semilattice_inf`. -/
def of (α : Type*) [semilattice_inf α] [order_top α] : SemilatInf := ⟨α⟩

@[simp] lemma coe_of (α : Type*) [semilattice_inf α] [order_top α] : ↥(of α) = α := rfl

instance : inhabited SemilatInf := ⟨of punit⟩

instance : large_category.{u} SemilatInf :=
{ hom := λ X Y, inf_top_hom X Y,
  id := λ X, inf_top_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, inf_top_hom.comp_id,
  comp_id' := λ X Y, inf_top_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, inf_top_hom.comp_assoc _ _ _ }

instance : concrete_category SemilatInf :=
{ forget := { obj := SemilatInf.X, map := λ X Y, coe_fn },
  forget_faithful := ⟨λ X Y, fun_like.coe_injective⟩ }

instance has_forget_to_PartOrd : has_forget₂ SemilatInf PartOrd :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f } }

@[simp] lemma coe_forget_to_PartOrd (X : SemilatInf) :
  ↥((forget₂ SemilatInf PartOrd).obj X) = ↥X := rfl

end SemilatInf

/-! ### Order dual -/

namespace SemilatSup

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : SemilatSup.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : SemilatSup ⥤ SemilatInf :=
{ obj := λ X, SemilatInf.of Xᵒᵈ, map := λ X Y, sup_bot_hom.dual }

end SemilatSup

namespace SemilatInf

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : SemilatInf.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : SemilatInf ⥤ SemilatSup :=
{ obj := λ X, SemilatSup.of Xᵒᵈ, map := λ X Y, inf_top_hom.dual }

end SemilatInf

/-- The equivalence between `SemilatSup` and `SemilatInf` induced by `order_dual` both ways.
-/
@[simps functor inverse]
def SemilatSup_equiv_SemilatInf : SemilatSup ≌ SemilatInf :=
equivalence.mk SemilatSup.dual SemilatInf.dual
  (nat_iso.of_components (λ X, SemilatSup.iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, SemilatInf.iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

lemma SemilatSup_dual_comp_forget_to_PartOrd :
  SemilatSup.dual ⋙ forget₂ SemilatInf PartOrd =
    forget₂ SemilatSup PartOrd ⋙ PartOrd.dual := rfl

lemma SemilatInf_dual_comp_forget_to_PartOrd :
  SemilatInf.dual ⋙ forget₂ SemilatSup PartOrd =
    forget₂ SemilatInf PartOrd ⋙ PartOrd.dual := rfl
