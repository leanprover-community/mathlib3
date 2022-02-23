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
-/

universes u
open category_theory

instance order_iso_class.to_top_hom_class {F α β : Type*} [partial_order α] [order_top α]
  [partial_order β] [order_top β] [order_iso_class F α β] :
  top_hom_class F α β :=
⟨λ f, top_le_iff.1 sorry⟩

instance order_iso_class.to_bot_hom_class {F α β : Type*} [partial_order α] [order_bot α]
  [partial_order β] [order_bot β] [order_iso_class F α β] :
  bot_hom_class F α β :=
⟨λ f, le_bot_iff.1 sorry⟩

instance order_iso_class.to_sup_hom_class {F α β : Type*} [semilattice_sup α] [semilattice_sup β]
  [order_iso_class F α β] :
  sup_hom_class F α β :=
⟨λ f a b, eq_of_forall_ge_iff $ λ c, sorry⟩

instance order_iso_class.to_inf_hom_class {F α β : Type*} [semilattice_inf α] [semilattice_inf β]
  [order_iso_class F α β] :
  inf_hom_class F α β :=
⟨λ f a b, eq_of_forall_le_iff $ λ c, sorry⟩

instance order_iso_class.to_sup_bot_hom_class {F α β : Type*} [semilattice_sup α] [order_bot α]
  [semilattice_sup β] [order_bot β] [order_iso_class F α β] :
  sup_bot_hom_class F α β :=
{ ..order_iso_class.to_sup_hom_class, ..order_iso_class.to_bot_hom_class }

instance order_iso_class.to_inf_top_hom_class {F α β : Type*} [semilattice_inf α] [order_top α]
  [semilattice_inf β] [order_top β] [order_iso_class F α β] :
  inf_top_hom_class F α β :=
{ ..order_iso_class.to_inf_hom_class, ..order_iso_class.to_top_hom_class }

def sup_hom.dual {α β : Type*} [has_sup α] [has_sup β] :
  sup_hom α β ≃ inf_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f, f.map_sup'⟩,
  inv_fun := λ f, ⟨f, f.map_inf'⟩,
  left_inv := λ f, sup_hom.ext $ λ _, rfl,
  right_inv := λ f, inf_hom.ext $ λ _, rfl }

def inf_hom.dual {α β : Type*} [has_inf α] [has_inf β] :
  inf_hom α β ≃ sup_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f, f.map_inf'⟩,
  inv_fun := λ f, ⟨f, f.map_sup'⟩,
  left_inv := λ f, inf_hom.ext $ λ _, rfl,
  right_inv := λ f, sup_hom.ext $ λ _, rfl }

def top_hom.dual {α β : Type*} [has_top α] [has_top β] :
  top_hom α β ≃ bot_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f, f.map_top'⟩,
  inv_fun := λ f, ⟨f, f.map_bot'⟩,
  left_inv := λ f, top_hom.ext $ λ _, rfl,
  right_inv := λ f, bot_hom.ext $ λ _, rfl }

def bot_hom.dual {α β : Type*} [has_bot α] [has_bot β] :
  bot_hom α β ≃ top_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f, f.map_bot'⟩,
  inv_fun := λ f, ⟨f, f.map_top'⟩,
  left_inv := λ f, bot_hom.ext $ λ _, rfl,
  right_inv := λ f, top_hom.ext $ λ _, rfl }

def sup_bot_hom.dual {α β : Type*} [has_sup α] [has_bot α] [has_sup β] [has_bot β] :
  sup_bot_hom α β ≃ inf_top_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f.to_sup_hom.dual, f.map_bot'⟩,
  inv_fun := λ f, ⟨sup_hom.dual.symm f.to_inf_hom, f.map_top'⟩,
  left_inv := λ f, sup_bot_hom.ext $ λ _, rfl,
  right_inv := λ f, inf_top_hom.ext $ λ _, rfl }

def inf_top_hom.dual {α β : Type*} [has_inf α] [has_top α] [has_inf β] [has_top β] :
  inf_top_hom α β ≃ sup_bot_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, ⟨f.to_inf_hom.dual, f.map_top'⟩,
  inv_fun := λ f, ⟨inf_hom.dual.symm f.to_sup_hom, f.map_bot'⟩,
  left_inv := λ f, inf_top_hom.ext $ λ _, rfl,
  right_inv := λ f, sup_bot_hom.ext $ λ _, rfl }


/-- The category of sup-semilattices with a bottom element. -/
structure SemilatticeSup : Type.{u + 1} :=
(X : Type.{u})
[is_semilattice_sup : semilattice_sup X]
[is_order_bot : order_bot X]

/-- The category of inf-semilattices with a top element. -/
structure SemilatticeInf : Type.{u + 1} :=
(X : Type.{u})
[is_semilattice_inf : semilattice_inf X]
[is_order_top : order_top X]

namespace SemilatticeSup

instance : has_coe_to_sort SemilatticeSup Type* := ⟨X⟩

attribute [protected] X
attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatticeSup` from a `semilattice_sup`. -/
def of (α : Type*) [semilattice_sup α] [order_bot α] : SemilatticeSup := ⟨α⟩

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
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

end SemilatticeSup

namespace SemilatticeInf

instance : has_coe_to_sort SemilatticeInf Type* := ⟨X⟩

attribute [protected] X
attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatticeInf` from a `semilattice_inf`. -/
def of (α : Type*) [semilattice_inf α] [order_top α] : SemilatticeInf := ⟨α⟩

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
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

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
{ obj := λ X, SemilatticeInf.of (order_dual X), map := λ X Y, sup_bot_hom.dual }

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
{ obj := λ X, SemilatticeSup.of (order_dual X), map := λ X Y, inf_top_hom.dual }

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
    forget₂ SemilatticeSup PartialOrder ⋙ PartialOrder.to_dual := rfl

lemma SemilatticeInf_dual_comp_forget_to_PartialOrder :
  SemilatticeInf.dual ⋙ forget₂ SemilatticeSup PartialOrder =
    forget₂ SemilatticeInf PartialOrder ⋙ PartialOrder.to_dual := rfl
