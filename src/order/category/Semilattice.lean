/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.PartialOrder
import order.hom.lattice

/-!
# The categories of semilattices

This defines `SemilatticeSup` and `SemilatticeInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/

universes u
open category_theory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatticeSup : Type.{u+1} :=
(X : Type.{u})
[is_semilattice_sup : semilattice_sup X]
[is_order_bot : order_bot X]

/-- The category of inf-semilattices with a top element. -/
structure SemilatticeInf : Type.{u+1} :=
(X : Type.{u})
[is_semilattice_inf : semilattice_inf X]
[is_order_top : order_top X]

attribute [protected] SemilatticeSup.X SemilatticeInf.X

namespace SemilatticeSup

instance : has_coe_to_sort SemilatticeSup Type* := ⟨SemilatticeSup.X⟩
attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatticeSup` from a `semilattice_sup`. -/
def of (α : Type*) [semilattice_sup α] [order_bot α] : SemilatticeSup := ⟨α⟩

@[simp] lemma coe_of (α : Type*) [semilattice_sup α] [order_bot α] : ↥(of α) = α := rfl

instance : inhabited SemilatticeSup := ⟨of punit⟩

instance : large_category.{u} SemilatticeSup :=
{ hom := λ X Y, sup_bot_hom X Y,
  id := λ X, sup_bot_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, sup_bot_hom.comp_id,
  comp_id' := λ X Y, sup_bot_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, sup_bot_hom.comp_assoc _ _ _ }

instance : concrete_category SemilatticeSup :=
{ forget := { obj := SemilatticeSup.X, map := λ X Y, coe_fn },
  forget_faithful := ⟨λ X Y, fun_like.coe_injective⟩ }

instance has_forget_to_PartialOrder : has_forget₂ SemilatticeSup PartialOrder :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f } }

@[simp] lemma coe_forget_to_PartialOrder (X : SemilatticeSup) :
  ↥((forget₂ SemilatticeSup PartialOrder).obj X) = ↥X := rfl

end SemilatticeSup

namespace SemilatticeInf

instance : has_coe_to_sort SemilatticeInf Type* := ⟨SemilatticeInf.X⟩

attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatticeInf` from a `semilattice_inf`. -/
def of (α : Type*) [semilattice_inf α] [order_top α] : SemilatticeInf := ⟨α⟩

@[simp] lemma coe_of (α : Type*) [semilattice_inf α] [order_top α] : ↥(of α) = α := rfl

instance : inhabited SemilatticeInf := ⟨of punit⟩

instance : large_category.{u} SemilatticeInf :=
{ hom := λ X Y, inf_top_hom X Y,
  id := λ X, inf_top_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, inf_top_hom.comp_id,
  comp_id' := λ X Y, inf_top_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, inf_top_hom.comp_assoc _ _ _ }

instance : concrete_category SemilatticeInf :=
{ forget := { obj := SemilatticeInf.X, map := λ X Y, coe_fn },
  forget_faithful := ⟨λ X Y, fun_like.coe_injective⟩ }

instance has_forget_to_PartialOrder : has_forget₂ SemilatticeInf PartialOrder :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f } }

@[simp] lemma coe_forget_to_PartialOrder (X : SemilatticeInf) :
  ↥((forget₂ SemilatticeInf PartialOrder).obj X) = ↥X := rfl

end SemilatticeInf

/-! ### Order dual -/

namespace SemilatticeSup

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : SemilatticeSup.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : SemilatticeSup ⥤ SemilatticeInf :=
{ obj := λ X, SemilatticeInf.of Xᵒᵈ, map := λ X Y, sup_bot_hom.dual }

end SemilatticeSup

namespace SemilatticeInf

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : SemilatticeInf.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : SemilatticeInf ⥤ SemilatticeSup :=
{ obj := λ X, SemilatticeSup.of Xᵒᵈ, map := λ X Y, inf_top_hom.dual }

end SemilatticeInf

/-- The equivalence between `SemilatticeSup` and `SemilatticeInf` induced by `order_dual` both ways.
-/
@[simps functor inverse]
def SemilatticeSup_equiv_SemilatticeInf : SemilatticeSup ≌ SemilatticeInf :=
equivalence.mk SemilatticeSup.dual SemilatticeInf.dual
  (nat_iso.of_components (λ X, SemilatticeSup.iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, SemilatticeInf.iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

lemma SemilatticeSup_dual_comp_forget_to_PartialOrder :
  SemilatticeSup.dual ⋙ forget₂ SemilatticeInf PartialOrder =
    forget₂ SemilatticeSup PartialOrder ⋙ PartialOrder.dual := rfl

lemma SemilatticeInf_dual_comp_forget_to_PartialOrder :
  SemilatticeInf.dual ⋙ forget₂ SemilatticeSup PartialOrder =
    forget₂ SemilatticeInf PartialOrder ⋙ PartialOrder.dual := rfl
