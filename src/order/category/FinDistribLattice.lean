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

This defines `FinDistribLattice`, the category of finite distributive lattices.
-/

universes u v

open category_theory

instance : distrib_lattice bool := linear_order.to_distrib_lattice

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinDistribLattice :=
(to_BoundedDistribLattice : BoundedDistribLattice)
[is_fintype : fintype to_BoundedDistribLattice]

namespace FinDistribLattice

instance : has_coe_to_sort FinDistribLattice Type* := ⟨λ X, X.to_BoundedDistribLattice⟩
instance (X : FinDistribLattice) : distrib_lattice X :=
X.to_BoundedDistribLattice.to_DistribLattice.str
instance (X : FinDistribLattice) : bounded_order X := X.to_BoundedDistribLattice.is_bounded_order

attribute [instance]  FinDistribLattice.is_fintype

/-- Construct a bundled `FinDistribLattice` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [fintype α] [nonempty α] : FinDistribLattice :=
by { haveI := fintype.to_bounded_order α, exact ⟨⟨⟨α⟩⟩⟩ }

instance : inhabited FinDistribLattice := ⟨of punit⟩

instance large_category : large_category FinDistribLattice :=
induced_category.category FinDistribLattice.to_BoundedDistribLattice

instance concrete_category : concrete_category FinDistribLattice :=
induced_category.concrete_category FinDistribLattice.to_BoundedDistribLattice

instance has_forget_to_BoundedDistribLattice :
  has_forget₂ FinDistribLattice BoundedDistribLattice :=
induced_category.has_forget₂ FinDistribLattice.to_BoundedDistribLattice

instance has_forget_to_FinPartialOrder : has_forget₂ FinDistribLattice FinPartialOrder :=
{ forget₂ := { obj := λ X, ⟨⟨X⟩⟩, map := λ X Y f, f },
  forget_comp := rfl }

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : FinDistribLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def to_dual : FinDistribLattice ⥤ FinDistribLattice :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `FinDistribLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : FinDistribLattice ≌ FinDistribLattice :=
equivalence.mk to_dual to_dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinDistribLattice

lemma FinDistribLattice_to_dual_comp_forget_to_DistribLattice :
  FinDistribLattice.to_dual ⋙ forget₂ FinDistribLattice DistribLattice =
    forget₂ FinDistribLattice DistribLattice ⋙ DistribLattice.to_dual := rfl

end FinDistribLattice
