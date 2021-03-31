/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.PartialOrder

/-! # Category of linearly ordered types -/

open category_theory

/-- The category of linearly ordered types. -/
def LinearOrder := bundled linear_order

namespace LinearOrder

instance : bundled_hom.parent_projection @linear_order.to_partial_order := ⟨⟩

attribute [derive [large_category, concrete_category]] LinearOrder

instance : has_coe_to_sort LinearOrder Type* := bundled.has_coe_to_sort

/-- Construct a bundled LinearOrder from the underlying type and typeclass. -/
def of (α : Type*) [linear_order α] : LinearOrder := bundled.of α

instance : inhabited LinearOrder := ⟨of punit⟩

instance (α : LinearOrder) : linear_order α := α.str

end LinearOrder
