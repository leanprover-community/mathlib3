/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import order.category.PartialOrder

/-! # Category of linearly ordered types -/

open category_theory

def LinearOrder := bundled linear_order

namespace LinearOrder

instance : bundled_hom.parent_projection @linear_order.to_partial_order := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] LinearOrder

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (α : Type*) [linear_order α] : LinearOrder := bundled.of α

instance : inhabited LinearOrder := ⟨of punit⟩

end LinearOrder
