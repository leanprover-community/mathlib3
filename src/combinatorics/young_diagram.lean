/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import order.upper_lower
import data.finset.preimage

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
- `young_diagram.row` and `young_diagram.row_len`: (lengths of) rows of a Young a diagram
- `young_diagram.col` and `young_diagram.col_len`: (lengths of) columns of a Young diagram

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `young_diagram.up_left_mem`.

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
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
lemma up_left_mem (μ : young_diagram) {i1 i2 j1 j2 : ℕ}
  (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
μ.is_lower_set (prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section distrib_lattice

@[simp] lemma cells_subset_iff {μ ν : young_diagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν := iff.rfl
@[simp] lemma cells_ssubset_iff {μ ν : young_diagram} : μ.cells ⊂ ν.cells ↔ μ < ν := iff.rfl

instance : has_sup young_diagram :=
{ sup := λ μ ν, { cells        := μ.cells ∪ ν.cells,
                  is_lower_set := by { rw finset.coe_union,
                                       exact μ.is_lower_set.union ν.is_lower_set } } }

@[simp] lemma cells_sup (μ ν : young_diagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells := rfl

@[simp, norm_cast] lemma coe_sup (μ ν : young_diagram) : ↑(μ ⊔ ν) = (μ ∪ ν : set (ℕ × ℕ)) :=
finset.coe_union _ _

@[simp] lemma mem_sup {μ ν : young_diagram} {x : ℕ × ℕ} : x ∈ (μ ⊔ ν) ↔ x ∈ μ ∨ x ∈ ν :=
finset.mem_union

instance : has_inf young_diagram :=
{ inf := λ μ ν, { cells        := μ.cells ∩ ν.cells,
                  is_lower_set := by { rw finset.coe_inter,
                                       exact μ.is_lower_set.inter ν.is_lower_set } } }

@[simp] lemma cells_inf (μ ν : young_diagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells := rfl

@[simp, norm_cast] lemma coe_inf (μ ν : young_diagram) : ↑(μ ⊓ ν) = (μ ∩ ν : set (ℕ × ℕ)) :=
finset.coe_inter _ _

@[simp] lemma mem_inf {μ ν : young_diagram} {x : ℕ × ℕ} : x ∈ (μ ⊓ ν) ↔ x ∈ μ ∧ x ∈ ν :=
finset.mem_inter

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance : order_bot young_diagram :=
{ bot := { cells := ∅, is_lower_set := λ _ _ _, false.elim }, bot_le := λ _ _, false.elim }

@[simp] lemma cells_bot : (⊥ : young_diagram).cells = ∅ := rfl

@[simp, norm_cast] lemma coe_bot : ↑(⊥ : young_diagram) = (∅ : set (ℕ × ℕ)) := rfl

@[simp] lemma not_mem_bot (x : ℕ × ℕ) : x ∉ (⊥ : young_diagram) := finset.not_mem_empty x

instance : inhabited young_diagram := ⟨⊥⟩

instance : distrib_lattice young_diagram :=
function.injective.distrib_lattice
  young_diagram.cells
  (λ μ ν h, by rwa young_diagram.ext_iff)
  (λ _ _, rfl) (λ _ _, rfl)

end distrib_lattice

/-- Cardinality of a Young diagram -/
@[reducible] protected def card (μ : young_diagram) : ℕ := μ.cells.card

section transpose
/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. --/

def transpose (μ : young_diagram) : young_diagram :=
{ cells :=  (equiv.prod_comm _ _).finset_congr μ.cells,
  is_lower_set := λ _ _ h, by {
    simp only [finset.mem_coe, equiv.finset_congr_apply, finset.mem_map_equiv],
    intro hcell, apply μ.is_lower_set _ hcell, simp [h], } }

@[simp] lemma mem_transpose {μ : young_diagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ :=
by { change c ∈ μ.cells.map _ ↔ _, rw finset.mem_map_equiv, refl, }

@[simp] lemma transpose_eq_iff {μ ν : young_diagram} : μ.transpose = ν ↔ μ = ν.transpose :=
by { split; { rintro rfl, ext, simp } }

@[simp] lemma transpose_transpose {μ : young_diagram} : μ.transpose.transpose = μ :=
by rw transpose_eq_iff

-- This is effectively both directions of the iff statement below.
protected lemma le_of_transpose_le {μ ν : young_diagram} (h_le : μ.transpose ≤ ν) :
  μ ≤ ν.transpose :=
λ c hc, by { simp only [mem_transpose], apply h_le, simpa }

@[simp] lemma transpose_le_iff {μ ν : young_diagram} : μ.transpose ≤ ν ↔ μ ≤ ν.transpose :=
⟨ young_diagram.le_of_transpose_le,
  by { convert @young_diagram.le_of_transpose_le μ.transpose ν.transpose, simp } ⟩

/-- Transposing Young diagrams is an `order_iso`. -/
def transpose_order_iso : young_diagram ≃o young_diagram :=
⟨⟨transpose, transpose, λ _, by simp, λ _, by simp⟩, by simp⟩

end transpose

section rows
/-- Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.row_len`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.row_len i`
      2.  `μ.row i = {i} ×ˢ (finset.range (μ.row_len i))`
      3.  `μ.row_len i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.row_len i2 ≤ μ.row_len i1`

Note: #3 is not convenient for defining `μ.row_len`; instead, `μ.row_len` is defined
as the smallest `j` such that `(i, j) ∉ μ`. --/

def row (μ : young_diagram) (i : ℕ) : finset (ℕ × ℕ) := μ.cells.filter (λ c, c.fst = i)

lemma mem_row_iff {μ : young_diagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i :=
by simp [row]

protected lemma exists_not_mem_row (μ : young_diagram) (i : ℕ) : ∃ j, (i, j) ∉ μ.cells :=
begin
  obtain ⟨j, hj⟩ := infinite.exists_not_mem_finset
    ((μ.cells).preimage (prod.mk i) (λ _ _ _ _ h, by {cases h, refl})),
  rw finset.mem_preimage at hj, exact ⟨j, hj⟩,
end

/-- Length of a row of a Young diagram --/
def row_len (μ : young_diagram) (i : ℕ) : ℕ := nat.find $ μ.exists_not_mem_row i

lemma mem_iff_lt_row_len {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.row_len i :=
by { rw [row_len, nat.lt_find_iff], push_neg,
     exact ⟨λ h _ hmj, μ.up_left_mem (by refl) hmj h, λ h, h _ (by refl)⟩ }

lemma row_eq_prod {μ : young_diagram} {i : ℕ} : μ.row i = {i} ×ˢ (finset.range (μ.row_len i)) :=
by { ext ⟨a, b⟩,
     simp only [finset.mem_product, finset.mem_singleton, finset.mem_range,
                mem_row_iff, mem_iff_lt_row_len, and_comm, and.congr_right_iff],
     rintro rfl, refl }

lemma row_len_eq_card (μ : young_diagram) {i : ℕ} : μ.row_len i = (μ.row i).card :=
by simp [row_eq_prod]

lemma row_len_decr (μ : young_diagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.row_len i2 ≤ μ.row_len i1 :=
by { by_contra' h_lt, rw ← lt_self_iff_false (μ.row_len i1),
     rw ← mem_iff_lt_row_len at h_lt ⊢,
     exact μ.up_left_mem hi (by refl) h_lt }

end rows

section columns
/-- Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. --/

def col (μ : young_diagram) (j : ℕ) : finset (ℕ × ℕ) := μ.cells.filter (λ c, c.snd = j)

lemma mem_col_iff {μ : young_diagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j :=
by simp [col]

protected lemma exists_not_mem_col (μ : young_diagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells :=
by { obtain ⟨i, hi⟩ := infinite.exists_not_mem_finset
       ((μ.cells).preimage (λ i, prod.mk i j) (λ _ _ _ _ h, by {cases h, refl})),
     rw finset.mem_preimage at hi, exact ⟨i, hi⟩ }

/-- Length of a column of a Young diagram --/
def col_len (μ : young_diagram) (j : ℕ) : ℕ := nat.find $ μ.exists_not_mem_col j

lemma mem_iff_lt_col_len {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.col_len j :=
by { rw [col_len, nat.lt_find_iff], push_neg,
     exact ⟨λ h _ hmj, μ.up_left_mem hmj (by refl) h, λ h, h _ (by refl)⟩ }

lemma col_eq_prod {μ : young_diagram} {j : ℕ} : μ.col j = (finset.range (μ.col_len j)) ×ˢ {j} :=
by { ext ⟨a, b⟩,
     simp only [finset.mem_product, finset.mem_singleton, finset.mem_range,
                mem_col_iff, mem_iff_lt_col_len, and_comm, and.congr_right_iff],
     rintro rfl, refl }

lemma col_len_eq_card (μ : young_diagram) {j : ℕ} : μ.col_len j = (μ.col j).card :=
by simp [col_eq_prod]

lemma col_len_decr (μ : young_diagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.col_len j2 ≤ μ.col_len j1 :=
by { by_contra' h_lt, rw ← lt_self_iff_false (μ.col_len j1),
     rw ← mem_iff_lt_col_len at h_lt ⊢,
     exact μ.up_left_mem (by refl) hj h_lt }

end columns

end young_diagram
