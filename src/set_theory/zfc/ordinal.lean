import set_theory.zfc.basic
import order.well_founded_set

namespace Set

/-- A set is a von Neumann ordinal when it's well-founded with respect to `∈`, and every element is
a subset.-/
def is_ordinal (x : Set) : Prop := x.to_set.well_founded_on (∈) ∧ ∀ y ∈ x, y ⊆ x

theorem is_ordinal.well_founded_on {x : Set} (h : x.is_ordinal) : x.to_set.well_founded_on (∈) :=
h.1

theorem is_ordinal.subset_of_mem {x y : Set} (hx : x.is_ordinal) : y ∈ x → y ⊆ x :=
hx.2 y

@[simp] theorem empty_is_ordinal : is_ordinal ∅ := by refine ⟨_, λ y, _⟩; simp

/-- The successor of an ordinal `x` is `x ∪ {x}`. -/
def succ (x : Set) : Set := x ∪ {x}

@[simp] theorem succ_to_set (x : Set) : x.succ.to_set = insert x x.to_set :=
begin
  rw succ,
  simp,
end

theorem is_ordinal.succ {x : Set} (h : x.is_ordinal) : x.succ.is_ordinal :=
begin
  split,
  {

  }
end

end Set
