/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.category.BoundedDistribLattice
import order.category.FinPartialOrder

/-!
# The category of finite distributive lattices

This file defines `FinBoundedDistribLattice`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

universes u

open category_theory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBoundedDistribLattice :=
(to_BoundedDistribLattice : BoundedDistribLattice)
[is_fintype : fintype to_BoundedDistribLattice]

namespace FinBoundedDistribLattice

instance : has_coe_to_sort FinBoundedDistribLattice Type* := ⟨λ X, X.to_BoundedDistribLattice⟩
instance (X : FinBoundedDistribLattice) : distrib_lattice X :=
X.to_BoundedDistribLattice.to_DistribLattice.str
instance (X : FinBoundedDistribLattice) : bounded_order X := X.to_BoundedDistribLattice.is_bounded_order

attribute [instance]  FinBoundedDistribLattice.is_fintype

/-- Construct a bundled `FinBoundedDistribLattice` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] [fintype α] : FinBoundedDistribLattice :=
⟨⟨⟨α⟩⟩⟩

/-- Construct a bundled `FinBoundedDistribLattice` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type*) [distrib_lattice α] [fintype α] [nonempty α] : FinBoundedDistribLattice :=
by { haveI := fintype.to_bounded_order α, exact ⟨⟨⟨α⟩⟩⟩ }

instance : inhabited FinBoundedDistribLattice := ⟨of punit⟩

instance large_category : large_category FinBoundedDistribLattice :=
induced_category.category to_BoundedDistribLattice

instance concrete_category : concrete_category FinBoundedDistribLattice :=
induced_category.concrete_category to_BoundedDistribLattice

instance has_forget_to_BoundedDistribLattice :
  has_forget₂ FinBoundedDistribLattice BoundedDistribLattice :=
induced_category.has_forget₂ FinBoundedDistribLattice.to_BoundedDistribLattice
example {α β : Type*} [lattice α] [lattice β] [bounded_order α] [bounded_order β]
   (f : bounded_lattice_hom α β) : α →o β := f
instance has_forget_to_FinPartialOrder : has_forget₂ FinBoundedDistribLattice FinPartialOrder :=
{ forget₂ := { obj := λ X, FinPartialOrder.of X,
               map := λ X Y f, (show bounded_lattice_hom X Y, from f : X →o Y) } }

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : FinBoundedDistribLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

example {X Y : FinBoundedDistribLattice} : (X ⟶ Y) = bounded_lattice_hom X Y := rfl

example {X : FinBoundedDistribLattice} : of X = X := rfl

-- /-- `order_dual` as a functor. -/
-- @[simps] def dual : FinBoundedDistribLattice ⥤ FinBoundedDistribLattice :=
-- { obj := λ X, ⟨BoundedDistribLattice.dual.obj X.to_BoundedDistribLattice⟩, map := λ X Y, _ }

-- /-- The equivalence between `FinBoundedDistribLattice` and itself induced by `order_dual` both ways. -/
-- @[simps functor inverse] def dual_equiv : FinBoundedDistribLattice ≌ FinBoundedDistribLattice :=
-- equivalence.mk dual dual
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinBoundedDistribLattice

-- lemma FinBoundedDistribLattice_dual_comp_forget_to_DistribLattice :
--   FinBoundedDistribLattice.dual ⋙ forget₂ FinBoundedDistribLattice DistribLattice =
--     forget₂ FinBoundedDistribLattice DistribLattice ⋙ DistribLattice.dual := rfl
