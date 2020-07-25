/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import data.fintype.sort
import data.fin
import order.category.LinearOrder

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/

open category_theory

class nonempty_fin_lin_ord (α : Type*) extends fintype α, complete_linear_order α :=
[nonempty : nonempty α]

instance punit.nonempty_fin_lin_ord : nonempty_fin_lin_ord punit :=
by { refine_struct
{ nonempty := ⟨punit.star⟩,
  .. punit.decidable_linear_ordered_cancel_add_comm_monoid,
  .. punit.fintype };
{ intros, exact punit.star <|> exact dec_trivial }, }

def NonemptyFinLinOrd := bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd

instance : bundled_hom.parent_projection
  (λ (α : Type*) [i : nonempty_fin_lin_ord α],
    @decidable_linear_order.to_linear_order α
    (@complete_linear_order.to_decidable_linear_order α
    (@nonempty_fin_lin_ord.to_complete_linear_order α i))) := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] NonemptyFinLinOrd

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (α : Type*) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := bundled.of α

instance : inhabited NonemptyFinLinOrd := ⟨of punit⟩

instance (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord α := α.str

end NonemptyFinLinOrd
