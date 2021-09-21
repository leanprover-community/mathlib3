/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.preorder_hom
import category_theory.concrete_category
import algebra.punit_instances

/-! # Category of preorders -/

open category_theory

/-- The category of preorders. -/
def Preorder := bundled preorder

namespace Preorder

instance : bundled_hom @preorder_hom :=
{ to_fun := @preorder_hom.to_fun,
  id := @preorder_hom.id,
  comp := @preorder_hom.comp,
  hom_ext := @preorder_hom.ext }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Preorder

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type*) [preorder α] : Preorder := bundled.of α

instance : inhabited Preorder := ⟨of punit⟩

instance (α : Preorder) : preorder α := α.str

end Preorder
