/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import category_theory.category.Cat
import category_theory.category.preorder
import category_theory.concrete_category.bundled_hom
import order.hom.basic

/-!
# Category of preorders

This defines `Preorder`, the category of preorders with monotone maps.
-/

universe u

open category_theory

/-- The category of preorders. -/
def Preorder := bundled preorder

namespace Preorder

instance : bundled_hom @order_hom :=
{ to_fun := @order_hom.to_fun,
  id := @order_hom.id,
  comp := @order_hom.comp,
  hom_ext := @order_hom.ext }

attribute [derive [large_category, concrete_category]] Preorder

instance : has_coe_to_sort Preorder Type* := bundled.has_coe_to_sort

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type*) [preorder α] : Preorder := bundled.of α

@[simp] lemma coe_of (α : Type*) [preorder α] : ↥(of α) = α := rfl

instance : inhabited Preorder := ⟨of punit⟩

instance (α : Preorder) : preorder α := α.str

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : Preorder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def dual : Preorder ⥤ Preorder :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, order_hom.dual }

/-- The equivalence between `Preorder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : Preorder ≌ Preorder :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end Preorder

/--
The embedding of `Preorder` into `Cat`.
-/
@[simps]
def Preorder_to_Cat : Preorder.{u} ⥤ Cat :=
{ obj := λ X, Cat.of X.1,
  map := λ X Y f, f.monotone.functor,
  map_id' := λ X, begin apply category_theory.functor.ext, tidy end,
  map_comp' := λ X Y Z f g, begin apply category_theory.functor.ext, tidy end }

instance : faithful Preorder_to_Cat.{u} :=
{ map_injective' := λ X Y f g h, begin ext x, exact functor.congr_obj h x end }

instance : full Preorder_to_Cat.{u} :=
{ preimage := λ X Y f, ⟨f.obj, f.monotone⟩,
  witness' := λ X Y f, begin apply category_theory.functor.ext, tidy end }
