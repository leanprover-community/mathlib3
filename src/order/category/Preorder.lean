/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import category_theory.concrete_category.bundled_hom
import algebra.punit_instances
import order.hom.basic

/-! # Category of preorders -/

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

instance : inhabited Preorder := ⟨of punit⟩

instance (α : Preorder) : preorder α := α.str

def order_iso.dual_dual (α : Type*) [preorder α] : α ≃o order_dual (order_dual α) :=
order_iso.refl α

def order_hom.dual_dual (α : Type*) [preorder α] : α →o order_dual (order_dual α) :=
⟨id, monotone_id⟩

def order_hom.of_dual_dual (α : Type*) [preorder α] : order_dual (order_dual α) →o α :=
⟨id, monotone_id⟩

/-- The equivalence between `Preorder` and itself induced by `order_dual` both ways. -/
def dual_equiv : Preorder ≌ Preorder :=
{ functor := { obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual },
  inverse := { obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual },
  unit_iso := { hom := { app := λ X, order_iso.dual_dual X, naturality' := λ X Y f, rfl },
                inv := { app := λ X,
                           ((order_iso.dual_dual X).symm : order_dual (order_dual X) →o X),
                         naturality' := λ X Y f, rfl } },
  counit_iso := { hom := { app := λ X,
                             ((order_iso.dual_dual X).symm : order_dual (order_dual X) →o X),
                           naturality' := λ X Y f, rfl },
                  inv := { app := λ X, (order_iso.dual_dual X : X →o order_dual (order_dual X)),
                           naturality' := λ X Y f, rfl } } }

end Preorder
