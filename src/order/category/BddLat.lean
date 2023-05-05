/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.adjunction.opposites
import order.category.BddOrd
import order.category.Lat
import order.category.Semilat
import order.category.mathlib

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

universes u

open category_theory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLat :=
(to_Lat : Lat)
[is_bounded_order : bounded_order to_Lat]

namespace BddLat

instance : has_coe_to_sort BddLat Type* := ⟨λ X, X.to_Lat⟩
instance (X : BddLat) : lattice X := X.to_Lat.str

attribute [instance] BddLat.is_bounded_order

/-- Construct a bundled `BddLat` from `lattice` + `bounded_order`. -/
def of (α : Type*) [lattice α] [bounded_order α] : BddLat := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [lattice α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BddLat := ⟨of punit⟩

instance : large_category.{u} BddLat :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category BddLat :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_BddOrd : has_forget₂ BddLat BddOrd :=
{ forget₂ := { obj := λ X, BddOrd.of X,
               map := λ X Y, bounded_lattice_hom.to_bounded_order_hom } }

instance has_forget_to_Lat : has_forget₂ BddLat Lat :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom } }

instance has_forget_to_SemilatSup : has_forget₂ BddLat SemilatSup :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_sup_bot_hom } }

instance has_forget_to_SemilatInf : has_forget₂ BddLat SemilatInf :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_inf_top_hom } }

@[simp] lemma coe_forget_to_BddOrd (X : BddLat) :
  ↥((forget₂ BddLat BddOrd).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_Lat (X : BddLat) :
  ↥((forget₂ BddLat Lat).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_SemilatSup (X : BddLat) :
  ↥((forget₂ BddLat SemilatSup).obj X) = ↥X := rfl

@[simp] lemma coe_forget_to_SemilatInf (X : BddLat) :
  ↥((forget₂ BddLat SemilatInf).obj X) = ↥X := rfl

lemma forget_Lat_PartOrd_eq_forget_BddOrd_PartOrd :
  forget₂ BddLat Lat ⋙ forget₂ Lat PartOrd =
    forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd := rfl

lemma forget_SemilatSup_PartOrd_eq_forget_BddOrd_PartOrd :
  forget₂ BddLat SemilatSup ⋙ forget₂ SemilatSup PartOrd =
    forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd := rfl

lemma forget_SemilatInf_PartOrd_eq_forget_BddOrd_PartOrd :
  forget₂ BddLat SemilatInf ⋙ forget₂ SemilatInf PartOrd =
    forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd := rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BddLat ⥤ BddLat :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BddLat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BddLat ≌ BddLat :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BddLat

lemma BddLat_dual_comp_forget_to_BddOrd :
  BddLat.dual ⋙ forget₂ BddLat BddOrd =
    forget₂ BddLat BddOrd ⋙ BddOrd.dual := rfl

lemma BddLat_dual_comp_forget_to_Lat :
  BddLat.dual ⋙ forget₂ BddLat Lat =
    forget₂ BddLat Lat ⋙ Lat.dual := rfl

lemma BddLat_dual_comp_forget_to_SemilatSup :
  BddLat.dual ⋙ forget₂ BddLat SemilatSup =
    forget₂ BddLat SemilatInf ⋙ SemilatInf.dual := rfl

lemma BddLat_dual_comp_forget_to_SemilatInf :
  BddLat.dual ⋙ forget₂ BddLat SemilatInf =
    forget₂ BddLat SemilatSup ⋙ SemilatSup.dual := rfl

/--  The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def Lat_to_BddLat : Lat.{u} ⥤ BddLat :=
{ obj := λ X, BddLat.of $ with_top $ with_bot X,
  map := λ X Y, lattice_hom.with_top_with_bot,
  map_id' := λ X, lattice_hom.with_top_with_bot_id,
  map_comp' := λ X Y Z _ _, lattice_hom.with_top_with_bot_comp _ _ }

/-- `Lat_to_BddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`. -/
def Lat_to_BddLat_forget_adjunction :
  Lat_to_BddLat.{u} ⊣ forget₂ BddLat Lat :=
adjunction.mk_of_hom_equiv
  { hom_equiv := λ X Y,
    { to_fun := λ f,
      { to_fun := f ∘ some ∘ some,
        map_sup' := λ a b, (congr_arg f $ by refl).trans (f.map_sup' _ _),
        map_inf' := λ a b, (congr_arg f $ by refl).trans (f.map_inf' _ _) },
      inv_fun := lattice_hom.with_top_with_bot',
      left_inv := λ f, bounded_lattice_hom.ext $ λ a, match a with
          | none := f.map_top'.symm
          | some none := f.map_bot'.symm
          | some (some a) := rfl
        end,
      right_inv := λ f, lattice_hom.ext $ λ a, rfl },
  hom_equiv_naturality_left_symm' := λ X Y Z f g, bounded_lattice_hom.ext $ λ a, match a with
          | none := rfl
          | some none := rfl
          | some (some a) := rfl
        end,
  hom_equiv_naturality_right' := λ X Y Z f g, lattice_hom.ext $ λ a, rfl }

/-- `Lat_to_BddLat` and `order_dual` commute. -/
@[simps] def Lat_to_BddLat_comp_dual_iso_dual_comp_Lat_to_BddLat :
 (Lat_to_BddLat.{u} ⋙ BddLat.dual) ≅ (Lat.dual ⋙ Lat_to_BddLat) :=
adjunction.left_adjoint_uniq
    (Lat_to_BddLat_forget_adjunction.comp BddLat.dual_equiv.to_adjunction)
    (Lat.dual_equiv.to_adjunction.comp Lat_to_BddLat_forget_adjunction)
