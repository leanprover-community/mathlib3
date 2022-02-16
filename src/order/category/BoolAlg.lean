/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.category.BoundedDistribLattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

open order_dual opposite

--TODO@Yaël: Once we have Heyting algebras, we won't need to go through `boolean_algebra.of_core`
instance {α : Type*} [boolean_algebra α] : boolean_algebra (order_dual α) :=
boolean_algebra.of_core
{ compl := λ a, to_dual (of_dual a)ᶜ,
  inf_compl_le_bot := λ _, sup_compl_eq_top.ge,
  top_le_sup_compl := λ _, inf_compl_eq_bot.ge,
  ..order_dual.distrib_lattice α, ..order_dual.bounded_order α }

/-- `set.preimage` as a bounded lattice homomorphism. -/
def bounded_lattice_hom.set_preimage {α β : Type*} (f : α → β) :
  bounded_lattice_hom (set β) (set α) :=
{ to_fun := set.preimage f,
  map_sup' := λ s t, set.preimage_union,
  map_inf' := λ s t, set.preimage_inter,
  map_top' := set.preimage_univ,
  map_bot' := set.preimage_empty }

universes u

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

instance : inhabited BoolAlg := ⟨of punit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def to_BoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice := BoundedDistribLattice.of X

instance : large_category.{u} BoolAlg := induced_category.category to_BoundedDistribLattice
instance : concrete_category BoolAlg := induced_category.concrete_category to_BoundedDistribLattice

instance has_forget_to_BoundedDistribLattice : has_forget₂ BoolAlg BoundedDistribLattice :=
induced_category.has_forget₂ to_BoundedDistribLattice

/-- Constructs an equivalence between boolean algebras from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoolAlg ⥤ BoolAlg :=
{ obj := λ X, of (order_dual X), map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoolAlg ≌ BoolAlg :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoolAlg

lemma BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
  BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
    forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual := rfl

/-- The powerset functor. `set` as a functor. -/
def Type_to_BoolAlg : Type* ⥤ BoolAlgᵒᵖ :=
{ obj := λ X, op $ BoolAlg.of (set X),
  map := λ X Y f, quiver.hom.op $ bounded_lattice_hom.set_preimage f }
