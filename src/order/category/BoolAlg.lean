/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.atoms
import order.category.BoundedDistribLattice
import order.hom.complete_lattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

open order_dual opposite set

universes u

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

@[simp] lemma coe_of (α : Type*) [boolean_algebra α] : ↥(of α) = α := rfl

instance : inhabited BoolAlg := ⟨of punit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def to_BoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice := BoundedDistribLattice.of X

@[simp] lemma coe_to_BoundedDistribLattice (X : BoolAlg) : ↥X.to_BoundedDistribLattice = ↥X := rfl

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

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoolAlg ≌ BoolAlg :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoolAlg

lemma BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
  BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
    forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual := rfl

/-! ### Atoms -/

/-- The type of atoms of an order. -/
@[nolint inhabited_instance] def atom (α : Type*) [preorder α] [order_bot α] := {a : α // is_atom a}

namespace atom
variables {α β : Type*}


section preorder
variables [preorder α] [order_bot α] [preorder β] [order_bot β]

instance : has_coe (atom α) α := coe_subtype

@[nolint duplicated_namespace] protected lemma atom (a : atom α) : is_atom (a : α) := a.2

@[ext] protected lemma ext {a b : atom α} (h : (a : α) = b) : a = b := subtype.ext h

end preorder

variables [lattice α] [bounded_order α] [lattice β] [bounded_order β]

def comap (f : bounded_lattice_hom α β) (b : atom β) : atom α := sorry

end atom

/-- The powerset functor. `set` as a functor. -/
def Type_to_BoolAlg : Type* ⥤ BoolAlgᵒᵖ :=
{ obj := λ X, op $ BoolAlg.of (set X),
  map := λ X Y f, quiver.hom.op $
    (complete_lattice_hom.set_preimage f : bounded_lattice_hom (set Y) (set X)) }

/-- The atoms functor. `atom` as a functor. -/
def BoolAlg_op_to_Type : BoolAlgᵒᵖ ⥤ Type* :=
{ obj := λ X, atom (unop X : BoolAlg),
  map := λ X Y f,
    sorry
    -- atom.comap $ quiver.hom.unop f
     }
