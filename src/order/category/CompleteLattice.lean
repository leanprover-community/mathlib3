/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BoundedLattice
import order.hom.complete_lattice

/-!
# The category of complete lattices

This file defines `CompleteLattice`, the category of complete lattices.
-/

universes u

open category_theory

/-- The category of complete lattices. -/
def CompleteLattice := bundled complete_lattice

namespace CompleteLattice

instance : has_coe_to_sort CompleteLattice Type* := bundled.has_coe_to_sort
instance (X : CompleteLattice) : complete_lattice X := X.str

/-- Construct a bundled `CompleteLattice` from a `complete_lattice`. -/
def of (α : Type*) [complete_lattice α] : CompleteLattice := bundled.of α

@[simp] lemma coe_of (α : Type*) [complete_lattice α] : ↥(of α) = α := rfl

instance : inhabited CompleteLattice := ⟨of punit⟩

instance : bundled_hom @complete_lattice_hom :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @complete_lattice_hom.id,
  comp := @complete_lattice_hom.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }
instance : large_category.{u} CompleteLattice := bundled_hom.category complete_lattice_hom
instance : concrete_category CompleteLattice := bundled_hom.concrete_category complete_lattice_hom

instance has_forget_to_BoundedLattice : has_forget₂ CompleteLattice BoundedLattice :=
{ forget₂ := { obj := λ X, BoundedLattice.of X,
               map := λ X Y, complete_lattice_hom.to_bounded_lattice_hom },
  forget_comp := rfl }

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : CompleteLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : CompleteLattice ⥤ CompleteLattice :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, complete_lattice_hom.dual }

/-- The equivalence between `CompleteLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : CompleteLattice ≌ CompleteLattice :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end CompleteLattice

lemma CompleteLattice_dual_comp_forget_to_BoundedLattice :
  CompleteLattice.dual ⋙ forget₂ CompleteLattice BoundedLattice =
    forget₂ CompleteLattice BoundedLattice ⋙ BoundedLattice.dual := rfl
