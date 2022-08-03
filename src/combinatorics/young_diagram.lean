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
  - `young_diagram.distrib_lattice`
  - `young_diagram.card` : the cardinality (number of boxes)

  - various constructors:
      `young_diagram.has_bot` : the empty Young diagram is (⊥ : young_diagram)

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

section distrib_lattice

instance young_diagram.has_le : has_le young_diagram :=
{ le := λ μ ν, (μ : set (ℕ × ℕ)) ⊆ ν }

instance young_diagram.has_sup : has_sup young_diagram :=
{ sup := λ μ ν, { cells        := μ.cells ∪ ν.cells,
                  is_lower_set := by { rw finset.coe_union,
                                       exact is_lower_set.union μ.is_lower_set ν.is_lower_set } } }

instance young_diagram.has_inf : has_inf young_diagram :=
{ inf := λ μ ν, { cells        := μ.cells ∩ ν.cells,
                  is_lower_set := by { rw finset.coe_inter,
                                       exact is_lower_set.inter μ.is_lower_set ν.is_lower_set } } }

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance young_diagram.has_bot : has_bot young_diagram :=
{ bot := { cells := finset.empty, is_lower_set := λ _ _ _ h, h } }

instance young_diagram.distrib_lattice : distrib_lattice young_diagram :=
function.injective.distrib_lattice
  (λ (μ : young_diagram), μ.cells)
  (λ μ ν h, by rwa young_diagram.ext_iff)
  (λ _ _, rfl) (λ _ _, rfl)

instance : inhabited young_diagram := ⟨⊥⟩

end distrib_lattice

/-- Cardinality of a Young diagram -/
def young_diagram.card (μ : young_diagram) : ℕ := μ.cells.card
lemma young_diagram.card_def (μ : young_diagram) : μ.card = μ.cells.card := rfl

@[simp] lemma μ_bot_card : (⊥ : young_diagram).card = 0 := rfl

end young_diagram
