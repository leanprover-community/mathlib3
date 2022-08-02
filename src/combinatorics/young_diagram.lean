/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/

import tactic
import data.set_like.basic
import data.set.basic
import order.upper_lower

/-!
# Young diagrams

A Young diagram is a finite set of up-left justified boxes:

[5, 3, 3, 1]
□□□□□
□□□
□□□
□

Equivalently, a lower set in ℕ × ℕ in the product partial order.

## Main functions:

  - basic properties and definitions involving shape, size, row and column
    lengths, and corners of a Young diagram

  - [TODO] various constructors:
      [young_diagram.has_empty]
      [young_diagram.of_row_lens]
      [young_diagram.outer_corner.add]
      [young_diagram.inner_corner.del]

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

section young_diagram

@[ext] structure young_diagram :=
  (cells : finset (ℕ × ℕ))
  (is_lower_set : is_lower_set (cells : set (ℕ × ℕ)))

instance young_diagram.set_like : set_like young_diagram (ℕ × ℕ) :=
{ coe := λ μ, (μ.cells : set (ℕ × ℕ)),
  coe_injective' := λ μ ν h, by { rwa [young_diagram.ext_iff, ← finset.coe_inj],} }

@[simp] lemma young_diagram.mem_cells {μ : young_diagram} (c : ℕ × ℕ) :
  c ∈ μ.cells ↔ c ∈ μ := iff.rfl

def young_diagram.nw_of (μ : young_diagram)
  {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) :
  (i1, j1) ∈ μ := μ.is_lower_set (prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

instance young_diagram.has_subset : has_subset young_diagram :=
  { subset := λ μ ν, μ.cells ⊆ ν.cells }

def young_diagram.card (μ : young_diagram) : ℕ := μ.cells.card
lemma young_diagram.card_def (μ : young_diagram) {i : ℕ} : μ.card = μ.cells.card := rfl


section μ_empty

/- The empty Young diagram -/

instance young_diagram.has_emptyc : has_emptyc young_diagram :=
{ emptyc := { cells := finset.empty, is_lower_set := λ _ _ _ h, h, } }

def μ_empty := (∅ : young_diagram)
@[simp] lemma μ_empty_card : (∅ : young_diagram).card = 0 := rfl

end μ_empty

end young_diagram
