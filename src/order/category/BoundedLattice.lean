/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BoundedOrder
import order.category.Lattice
import order.category.Semilattice

/-!
# The category of bounded lattices

This file defines `BoundedLattice`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

universes u

open category_theory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BoundedLattice :=
(to_Lattice : Lattice)
[is_bounded_order : bounded_order to_Lattice]

namespace BoundedLattice

instance : has_coe_to_sort BoundedLattice Type* := ⟨λ X, X.to_Lattice⟩
instance (X : BoundedLattice) : lattice X := X.to_Lattice.str

attribute [instance] BoundedLattice.is_bounded_order

/-- Construct a bundled `BoundedLattice` from `lattice` + `bounded_order`. -/
def of (α : Type*) [lattice α] [bounded_order α] : BoundedLattice := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [lattice α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BoundedLattice := ⟨of punit⟩

instance : large_category.{u} BoundedLattice :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category BoundedLattice :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_BoundedOrder : has_forget₂ BoundedLattice BoundedOrder :=
{ forget₂ := { obj := λ X, BoundedOrder.of X,
               map := λ X Y, bounded_lattice_hom.to_bounded_order_hom } }

instance has_forget_to_Lattice : has_forget₂ BoundedLattice Lattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom } }

instance has_forget_to_SemilatticeSup : has_forget₂ BoundedLattice SemilatticeSup :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_sup_bot_hom } }

instance has_forget_to_SemilatticeInf : has_forget₂ BoundedLattice SemilatticeInf :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_inf_top_hom } }

@[simp] lemma coe_forget_to_BoundedOrder (X : BoundedLattice) :
  ↥((forget₂ BoundedLattice BoundedOrder).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_Lattice (X : BoundedLattice) :
  ↥((forget₂ BoundedLattice Lattice).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_SemilatticeSup (X : BoundedLattice) :
  ↥((forget₂ BoundedLattice SemilatticeSup).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_SemilatticeInf (X : BoundedLattice) :
  ↥((forget₂ BoundedLattice SemilatticeInf).obj X) = ↥X := rfl

lemma forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
  forget₂ BoundedLattice Lattice ⋙ forget₂ Lattice PartialOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ forget₂ BoundedOrder PartialOrder := rfl

lemma forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
  forget₂ BoundedLattice SemilatticeSup ⋙ forget₂ SemilatticeSup PartialOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ forget₂ BoundedOrder PartialOrder := rfl

lemma forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
  forget₂ BoundedLattice SemilatticeInf ⋙ forget₂ SemilatticeInf PartialOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ forget₂ BoundedOrder PartialOrder := rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoundedLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoundedLattice ⥤ BoundedLattice :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BoundedLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoundedLattice ≌ BoundedLattice :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoundedLattice

lemma BoundedLattice_dual_comp_forget_to_BoundedOrder :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice BoundedOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ BoundedOrder.dual := rfl

lemma BoundedLattice_dual_comp_forget_to_Lattice :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice Lattice =
    forget₂ BoundedLattice Lattice ⋙ Lattice.dual := rfl

lemma BoundedLattice_dual_comp_forget_to_SemilatticeSup :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeSup =
    forget₂ BoundedLattice SemilatticeInf ⋙ SemilatticeInf.dual := rfl

lemma BoundedLattice_dual_comp_forget_to_SemilatticeInf :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeInf =
    forget₂ BoundedLattice SemilatticeSup ⋙ SemilatticeSup.dual := rfl
