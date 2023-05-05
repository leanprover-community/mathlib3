/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.category.BddDistLat
import order.category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

universes u

open category_theory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLat :=
(to_BddDistLat : BddDistLat)
[is_fintype : fintype to_BddDistLat]

namespace FinBddDistLat

instance : has_coe_to_sort FinBddDistLat Type* := ⟨λ X, X.to_BddDistLat⟩
instance (X : FinBddDistLat) : distrib_lattice X :=
X.to_BddDistLat.to_DistLat.str
instance (X : FinBddDistLat) : bounded_order X := X.to_BddDistLat.is_bounded_order

attribute [instance]  FinBddDistLat.is_fintype

/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] [fintype α] : FinBddDistLat :=
⟨⟨⟨α⟩⟩⟩

/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type*) [distrib_lattice α] [fintype α] [nonempty α] : FinBddDistLat :=
by { haveI := fintype.to_bounded_order α, exact ⟨⟨⟨α⟩⟩⟩ }

instance : inhabited FinBddDistLat := ⟨of punit⟩

instance large_category : large_category FinBddDistLat :=
induced_category.category to_BddDistLat

instance concrete_category : concrete_category FinBddDistLat :=
induced_category.concrete_category to_BddDistLat

instance has_forget_to_BddDistLat :
  has_forget₂ FinBddDistLat BddDistLat :=
induced_category.has_forget₂ FinBddDistLat.to_BddDistLat
example {α β : Type*} [lattice α] [lattice β] [bounded_order α] [bounded_order β]
   (f : bounded_lattice_hom α β) : α →o β := f
instance has_forget_to_FinPartOrd : has_forget₂ FinBddDistLat FinPartOrd :=
{ forget₂ := { obj := λ X, FinPartOrd.of X,
               map := λ X Y f, (show bounded_lattice_hom X Y, from f : X →o Y) } }

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : FinBddDistLat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

example {X Y : FinBddDistLat} : (X ⟶ Y) = bounded_lattice_hom X Y := rfl

-- /-- `order_dual` as a functor. -/
-- @[simps] def dual : FinBddDistLat ⥤ FinBddDistLat :=
-- { obj := λ X, ⟨BddDistLat.dual.obj X.to_BddDistLat⟩, map := λ X Y, _ }

-- /-- The equivalence between `FinBddDistLat` and itself induced by `order_dual` both ways. -/
-- @[simps functor inverse] def dual_equiv : FinBddDistLat ≌ FinBddDistLat :=
-- equivalence.mk dual dual
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinBddDistLat

-- lemma FinBddDistLat_dual_comp_forget_to_DistLat :
--   FinBddDistLat.dual ⋙ forget₂ FinBddDistLat DistLat =
--     forget₂ FinBddDistLat DistLat ⋙ DistLat.dual := rfl
