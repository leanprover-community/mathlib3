/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.Preorder

/-! # Category of partially ordered types -/

open category_theory

/-- The category of partially ordered types. -/
def PartialOrder := bundled partial_order

namespace PartialOrder

instance : bundled_hom.parent_projection @partial_order.to_preorder := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] PartialOrder

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type*) [partial_order α] : PartialOrder := bundled.of α

instance : inhabited PartialOrder := ⟨of punit⟩

instance (α : PartialOrder) : partial_order α := α.str

end PartialOrder
