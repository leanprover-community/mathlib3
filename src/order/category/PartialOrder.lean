/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import order.category.Preorder

/-! # Category of partially ordered types -/

open category_theory

def PartialOrder := bundled partial_order

namespace PartialOrder

instance : bundled_hom.parent_projection @partial_order.to_preorder := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] PartialOrder

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (α : Type*) [partial_order α] : PartialOrder := bundled.of α

instance : inhabited PartialOrder := ⟨of punit⟩

end PartialOrder
