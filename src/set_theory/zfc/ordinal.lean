import set_theory.zfc.basic
import order.well_founded_set

namespace Set

def is_ordinal (x : Set) : Prop := x.to_set.well_founded_on (∈) ∧ ∀ y ∈ x, y ⊆ x

theorem is_ordinal.well_founded_on {x : Set} (h : x.is_ordinal) : x.to_set.well_founded_on (∈) :=
h.1

theorem is_ordinal.subset_of_mem {x y : Set} (hx : x.is_ordinal) : y ∈ x → y ⊆ x :=
hx.2 y

theorem empty_is_ordinal : is_ordinal ∅ :=
begin
  split,
  simp,
end

end Set
