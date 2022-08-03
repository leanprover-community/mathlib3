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

## Main functions:

  - `young_diagram` : basic definition
  - `young_diagram.card` : the cardinality (number of boxes)

  - various constructors:
      `young_diagram.has_emptyc` : the empty Young diagram

## Notation:

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left (northwest) of (i2, j2). This terminology is used
below, e.g. in `young_diagram.nw_of`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

section young_diagram

/-- A Young diagram is a lower set in ℕ × ℕ -/
@[ext] structure young_diagram :=
(cells : finset (ℕ × ℕ))
(is_lower_set : is_lower_set (cells : set (ℕ × ℕ)))

instance young_diagram.set_like : set_like young_diagram (ℕ × ℕ) :=
{ coe            := λ μ, (μ.cells : set (ℕ × ℕ)),
  coe_injective' := λ μ ν h, by { rwa [young_diagram.ext_iff, ← finset.coe_inj] } }

@[simp] lemma young_diagram.mem_cells {μ : young_diagram} (c : ℕ × ℕ) :
  c ∈ μ.cells ↔ c ∈ μ := iff.rfl

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left (northwest) of (i2, j2). -/
lemma young_diagram.nw_of (μ : young_diagram) {i1 i2 j1 j2 : ℕ}
  (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
μ.is_lower_set (prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

instance young_diagram.has_subset : has_subset young_diagram :=
{ subset := λ μ ν, (μ : set (ℕ × ℕ)) ⊆ ν }

/-- Cardinality of a Young diagram -/
def young_diagram.card (μ : young_diagram) : ℕ := μ.cells.card
lemma young_diagram.card_def (μ : young_diagram) : μ.card = μ.cells.card := rfl

/- (TODO) row and column lengths, and corners of a Young diagram.
   (TODO: the transpose of a `young_diagram`)
   (TODO: a `young_diagram` from a list of row or column lengths)
   (TODO: adding or removing a corner box from a `young_diagram`) -/

section μ_empty

/-! The empty Young diagram -/

instance young_diagram.has_emptyc : has_emptyc young_diagram :=
{ emptyc := { cells := finset.empty, is_lower_set := λ _ _ _ h, h } }

/-- The empty Young diagram -/
def μ_empty := (∅ : young_diagram)
@[simp] lemma μ_empty_card : (∅ : young_diagram).card = 0 := rfl

instance : inhabited young_diagram := ⟨∅⟩

end μ_empty

end young_diagram
