/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Lattice
import order.hom.complete_lattice

/-!
# The category of frames

This file defines `Frame`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

universes u

open category_theory order

/-- The category of frames. -/
def Frame := bundled frame

namespace Frame

instance : has_coe_to_sort Frame Type* := bundled.has_coe_to_sort
instance (X : Frame) : frame X := X.str

/-- Construct a bundled `Frame` from a `frame`. -/
def of (α : Type*) [frame α] : Frame := bundled.of α

instance : inhabited Frame := ⟨of punit⟩

instance : large_category.{u} Frame :=
{ hom := λ X Y, frame_hom X Y,
  id := λ X, frame_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, frame_hom.comp_id,
  comp_id' := λ X Y, frame_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, frame_hom.comp_assoc _ _ _ }

instance : concrete_category Frame :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_Lattice : has_forget₂ Frame Lattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, frame_hom.to_lattice_hom } }

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps] def iso.mk {α β : Frame.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end Frame
