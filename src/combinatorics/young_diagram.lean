/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import order.upper_lower

/-!
# Young diagrams

A Young diagram is a finite set of up-left justified boxes:

```text
□□□□□
□□□
□□□
□
```
This Young diagram corresponds to the [5, 3, 3, 1] partition of 12.

We represent it as a lower set in `ℕ × ℕ` in the product partial order. We write `(i, j) ∈ μ`
to say that `(i, j)` (in matrix coordinates) is in the Young diagram `μ`.

## Main definitions

- `young_diagram` : Young diagrams
- `young_diagram.card` : the number of cells in a Young diagram (its *cardinality*)
- `young_diagram.distrib_lattice` : a distributive lattice instance for Young diagrams
  ordered by containment, with `(⊥ : young_diagram)` the empty diagram.

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left (northwest) of (i2, j2). This terminology is used
below, e.g. in `young_diagram.nw_of`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

/-- A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever
a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell
is a cell in row `i` and column `j`, where rows are enumerated downward and columns rightward.

Young diagrams are modeled as finite sets in `ℕ × ℕ` that are lower sets with respect to the
standard order on products. -/
@[ext] structure young_diagram :=
(cells : finset (ℕ × ℕ))
(is_lower_set : is_lower_set (cells : set (ℕ × ℕ)))

namespace young_diagram

instance : set_like young_diagram (ℕ × ℕ) :=
{ coe            := coe young_diagram.cells,
  coe_injective' := λ μ ν h, by { rwa [young_diagram.ext_iff, ← finset.coe_inj] } }

@[simp] lemma mem_cells {μ : young_diagram} (c : ℕ × ℕ) :
  c ∈ μ.cells ↔ c ∈ μ := iff.rfl

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left (northwest) of (i2, j2). -/
lemma nw_of (μ : young_diagram) {i1 i2 j1 j2 : ℕ}
  (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
μ.is_lower_set (prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section distrib_lattice

@[simp] lemma cells_subset_iff (μ ν : young_diagram) : μ.cells ⊆ ν.cells ↔ μ ≤ ν := iff.rfl
@[simp] lemma cells_ssubset_iff (μ ν : young_diagram) : μ.cells ⊂ ν.cells ↔ μ < ν := iff.rfl

instance : has_sup young_diagram :=
{ sup := λ μ ν, { cells        := μ.cells ∪ ν.cells,
                  is_lower_set := by { rw finset.coe_union,
                                       exact μ.is_lower_set.union ν.is_lower_set } } }

@[simp] lemma cells_sup (μ ν : young_diagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells := rfl

@[simp, norm_cast] lemma coe_sup (μ ν : young_diagram) : ↑(μ ⊔ ν) = (μ ∪ ν : set (ℕ × ℕ)) :=
finset.coe_union _ _

instance : has_inf young_diagram :=
{ inf := λ μ ν, { cells        := μ.cells ∩ ν.cells,
                  is_lower_set := by { rw finset.coe_inter,
                                       exact μ.is_lower_set.inter ν.is_lower_set } } }

@[simp] lemma cells_inf (μ ν : young_diagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells := rfl

@[simp, norm_cast] lemma coe_inf (μ ν : young_diagram) : ↑(μ ⊓ ν) = (μ ∩ ν : set (ℕ × ℕ)) :=
finset.coe_inter _ _

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance : order_bot young_diagram :=
{ bot := { cells := ∅, is_lower_set := λ _ _ _, false.elim }, bot_le := λ _ _, false.elim }

@[simp] lemma cells_bot : (⊥ : young_diagram).cells = ∅ := rfl

@[simp, norm_cast] lemma coe_bot : ↑(⊥ : young_diagram) = (∅ : set (ℕ × ℕ)) := rfl

instance : inhabited young_diagram := ⟨⊥⟩

instance : distrib_lattice young_diagram :=
function.injective.distrib_lattice
  young_diagram.cells
  (λ μ ν h, by rwa young_diagram.ext_iff)
  (λ _ _, rfl) (λ _ _, rfl)

end distrib_lattice

/-- Cardinality of a Young diagram -/
@[reducible] protected def card (μ : young_diagram) : ℕ := μ.cells.card
lemma card_def (μ : young_diagram) : μ.card = μ.cells.card := rfl

@[simp] lemma card_bot : (⊥ : young_diagram).card = 0 := rfl

end young_diagram
