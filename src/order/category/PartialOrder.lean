/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.antisymmetrization
import order.category.Preorder

/-! # Category of partially ordered types -/

open category_theory

universe u

/-- The category of partially ordered types. -/
def PartialOrder := bundled partial_order

namespace PartialOrder

instance : bundled_hom.parent_projection @partial_order.to_preorder := ⟨⟩

attribute [derive [large_category, concrete_category]] PartialOrder

instance : has_coe_to_sort PartialOrder Type* := bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type*) [partial_order α] : PartialOrder := bundled.of α

instance : inhabited PartialOrder := ⟨of punit⟩

instance (α : PartialOrder) : partial_order α := α.str

end PartialOrder

local attribute [instance] le_equiv.setoid

--TODO@Yaël: I'm pretty sure this is the free functor. Prove the adjunction.
/-- `antisymmetrization` as a functor. -/
def Preorder_to_PartialOrder : Preorder.{u} ⥤ PartialOrder :=
{ obj := λ X, PartialOrder.of (antisymmetrization X),
  map := λ X Y f, f.antisymmetrization,
  map_id' := λ X, by { ext, exact quotient.induction_on x (λ x, quotient.map_mk _ (λ a b, id) _) },
  map_comp' := λ X Y Z f g,
    by { ext, exact quotient.induction_on x (λ x, order_hom.antisymmetrization_apply_mk _ _) } }
