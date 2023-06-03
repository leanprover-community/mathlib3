/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import order.upper_lower.basic
import data.finset.preimage

/-!
# Young diagrams

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
- `young_diagram.row` and `young_diagram.row_len`: rows of a Young diagram and their lengths
- `young_diagram.col` and `young_diagram.col_len`: columns of a Young diagram and their lengths

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `young_diagram.up_left_mem`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

open function

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

@[simp] lemma mem_mk (c : ℕ × ℕ) (cells) (is_lower_set) :
  c ∈ young_diagram.mk cells is_lower_set ↔ c ∈ cells := iff.rfl

instance decidable_mem (μ : young_diagram) : decidable_pred (∈ μ) :=
show decidable_pred (∈ μ.cells), by apply_instance

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

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
def transpose (μ : young_diagram) : young_diagram :=
{ cells :=  (equiv.prod_comm _ _).finset_congr μ.cells,
  is_lower_set := λ _ _ h, begin
    simp only [finset.mem_coe, equiv.finset_congr_apply, finset.mem_map_equiv],
    intro hcell,
    apply μ.is_lower_set _ hcell,
    simp [h],
  end }

@[simp] lemma mem_transpose {μ : young_diagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ :=
by simp [transpose]

@[simp] lemma transpose_transpose (μ : young_diagram) : μ.transpose.transpose = μ :=
by { ext, simp }

lemma transpose_eq_iff_eq_transpose {μ ν : young_diagram} :
  μ.transpose = ν ↔ μ = ν.transpose :=
by { split; { rintro rfl, simp } }

@[simp] lemma transpose_eq_iff {μ ν : young_diagram} :
  μ.transpose = ν.transpose ↔ μ = ν :=
by { rw transpose_eq_iff_eq_transpose, simp }

-- This is effectively both directions of `transpose_le_iff` below.
protected lemma le_of_transpose_le {μ ν : young_diagram} (h_le : μ.transpose ≤ ν) :
  μ ≤ ν.transpose :=
λ c hc, by { simp only [mem_transpose], apply h_le, simpa }

@[simp] lemma transpose_le_iff {μ ν : young_diagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
⟨ λ h, by { convert young_diagram.le_of_transpose_le h, simp },
  λ h, by { convert @young_diagram.le_of_transpose_le _ _ _, simpa } ⟩

@[mono]
protected lemma transpose_mono {μ ν : young_diagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
transpose_le_iff.mpr h_le

/-- Transposing Young diagrams is an `order_iso`. -/
@[simps] def transpose_order_iso : young_diagram ≃o young_diagram :=
⟨⟨transpose, transpose, λ _, by simp, λ _, by simp⟩, by simp⟩

end transpose

section rows
/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.row_len`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.row_len i`
      2.  `μ.row i = {i} ×ˢ (finset.range (μ.row_len i))`
      3.  `μ.row_len i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.row_len i2 ≤ μ.row_len i1`

Note: #3 is not convenient for defining `μ.row_len`; instead, `μ.row_len` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/

/-- The `i`-th row of a Young diagram consists of the cells whose first coordinate is `i`. -/
def row (μ : young_diagram) (i : ℕ) : finset (ℕ × ℕ) := μ.cells.filter (λ c, c.fst = i)

lemma mem_row_iff {μ : young_diagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i :=
by simp [row]

lemma mk_mem_row_iff {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ :=
by simp [row]

protected lemma exists_not_mem_row (μ : young_diagram) (i : ℕ) : ∃ j, (i, j) ∉ μ :=
begin
  obtain ⟨j, hj⟩ := infinite.exists_not_mem_finset
    ((μ.cells).preimage (prod.mk i) (λ _ _ _ _ h, by {cases h, refl})),
  rw finset.mem_preimage at hj,
  exact ⟨j, hj⟩,
end

/-- Length of a row of a Young diagram -/
def row_len (μ : young_diagram) (i : ℕ) : ℕ := nat.find $ μ.exists_not_mem_row i

lemma mem_iff_lt_row_len {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.row_len i :=
by { rw [row_len, nat.lt_find_iff], push_neg,
     exact ⟨λ h _ hmj, μ.up_left_mem (by refl) hmj h, λ h, h _ (by refl)⟩ }

lemma row_eq_prod {μ : young_diagram} {i : ℕ} : μ.row i = {i} ×ˢ finset.range (μ.row_len i) :=
by { ext ⟨a, b⟩,
     simp only [finset.mem_product, finset.mem_singleton, finset.mem_range,
                mem_row_iff, mem_iff_lt_row_len, and_comm, and.congr_right_iff],
     rintro rfl, refl }

lemma row_len_eq_card (μ : young_diagram) {i : ℕ} : μ.row_len i = (μ.row i).card :=
by simp [row_eq_prod]

@[mono]
lemma row_len_anti (μ : young_diagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.row_len i2 ≤ μ.row_len i1 :=
by { by_contra' h_lt, rw ← lt_self_iff_false (μ.row_len i1),
     rw ← mem_iff_lt_row_len at h_lt ⊢,
     exact μ.up_left_mem hi (by refl) h_lt }

end rows

section columns
/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/

/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : young_diagram) (j : ℕ) : finset (ℕ × ℕ) := μ.cells.filter (λ c, c.snd = j)

lemma mem_col_iff {μ : young_diagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j :=
by simp [col]

lemma mk_mem_col_iff {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ :=
by simp [col]

protected lemma exists_not_mem_col (μ : young_diagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells :=
by { convert μ.transpose.exists_not_mem_row j, simp }

/-- Length of a column of a Young diagram -/
def col_len (μ : young_diagram) (j : ℕ) : ℕ := nat.find $ μ.exists_not_mem_col j

@[simp] lemma col_len_transpose (μ : young_diagram) (j : ℕ) : μ.transpose.col_len j = μ.row_len j :=
by simp [row_len, col_len]

@[simp] lemma row_len_transpose (μ : young_diagram) (i : ℕ) : μ.transpose.row_len i = μ.col_len i :=
by simp [row_len, col_len]

lemma mem_iff_lt_col_len {μ : young_diagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.col_len j :=
by { rw [← row_len_transpose, ← mem_iff_lt_row_len], simp }

lemma col_eq_prod {μ : young_diagram} {j : ℕ} : μ.col j = (finset.range (μ.col_len j)) ×ˢ {j} :=
by { ext ⟨a, b⟩,
     simp only [finset.mem_product, finset.mem_singleton, finset.mem_range,
                mem_col_iff, mem_iff_lt_col_len, and_comm, and.congr_right_iff],
     rintro rfl, refl }

lemma col_len_eq_card (μ : young_diagram) {j : ℕ} : μ.col_len j = (μ.col j).card :=
by simp [col_eq_prod]

@[mono]
lemma col_len_anti (μ : young_diagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.col_len j2 ≤ μ.col_len j1 :=
by { convert μ.transpose.row_len_anti j1 j2 hj; simp }

end columns

section row_lens
/-! ### The list of row lengths of a Young diagram

This section defines `μ.row_lens : list ℕ`, the list of row lengths of a Young diagram `μ`.
  1. `young_diagram.row_lens_sorted` : It is weakly decreasing (`list.sorted (≥)`).
  2. `young_diagram.row_lens_pos` : It is strictly positive.

-/

/-- List of row lengths of a Young diagram -/
def row_lens (μ : young_diagram) : list ℕ := (list.range $ μ.col_len 0).map μ.row_len

@[simp] lemma nth_le_row_lens {μ : young_diagram} {i : ℕ} {hi : i < μ.row_lens.length} :
  μ.row_lens.nth_le i hi = μ.row_len i :=
by simp only [row_lens, list.nth_le_range, list.nth_le_map']

@[simp] lemma length_row_lens {μ : young_diagram} : μ.row_lens.length = μ.col_len 0 :=
by simp only [row_lens, list.length_map, list.length_range]

lemma row_lens_sorted (μ : young_diagram) : μ.row_lens.sorted (≥) :=
(list.pairwise_le_range _).map _ μ.row_len_anti

lemma pos_of_mem_row_lens (μ : young_diagram) (x : ℕ) (hx : x ∈ μ.row_lens) : 0 < x :=
begin
  rw [row_lens, list.mem_map] at hx,
  obtain ⟨i, hi, rfl : μ.row_len i = x⟩ := hx,
  rwa [list.mem_range, ← mem_iff_lt_col_len, mem_iff_lt_row_len] at hi
end

end row_lens

section equiv_list_row_lens
/-! ### Equivalence between Young diagrams and lists of natural numbers

This section defines the equivalence between Young diagrams `μ` and weakly decreasing lists `w`
of positive natural numbers, corresponding to row lengths of the diagram:
  `young_diagram.equiv_list_row_lens :`
  `young_diagram ≃ {w : list ℕ // w.sorted (≥) ∧ ∀ x ∈ w, 0 < x}`

The two directions are `young_diagram.row_lens` (defined above) and `young_diagram.of_row_lens`.

-/

/-- The cells making up a `young_diagram` from a list of row lengths -/
protected def cells_of_row_lens : list ℕ → finset (ℕ × ℕ)
| [] := ∅
| (w :: ws) := (({0} : finset ℕ) ×ˢ finset.range w) ∪
                 (cells_of_row_lens ws).map
                   (embedding.prod_map ⟨_, nat.succ_injective⟩ (embedding.refl ℕ))

protected lemma mem_cells_of_row_lens {w : list ℕ} {c : ℕ × ℕ} :
  c ∈ young_diagram.cells_of_row_lens w ↔ ∃ (h : c.fst < w.length), c.snd < w.nth_le c.fst h :=
begin
  induction w generalizing c;
  rw young_diagram.cells_of_row_lens,
  { simp [young_diagram.cells_of_row_lens] },
  { rcases c with ⟨⟨_, _⟩, _⟩,
    { simp },
    { simpa [w_ih, -finset.singleton_product, nat.succ_lt_succ_iff] } }
end

/-- Young diagram from a sorted list -/
def of_row_lens (w : list ℕ) (hw : w.sorted (≥)) : young_diagram :=
{ cells        := young_diagram.cells_of_row_lens w,
  is_lower_set := begin
    rintros ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ hcell,
    rw [finset.mem_coe, young_diagram.mem_cells_of_row_lens] at hcell ⊢,
    obtain ⟨h1, h2⟩ := hcell,
    refine ⟨hi.trans_lt h1, _⟩,
    calc j1 ≤ j2            : hj
      ...   < w.nth_le i2 _ : h2
      ...   ≤ w.nth_le i1 _ : _,
    obtain (rfl | h) := eq_or_lt_of_le hi,
    { refl },
    { apply list.pairwise_iff_nth_le.mp hw _ _ _ h }
  end }

lemma mem_of_row_lens {w : list ℕ} {hw : w.sorted (≥)} {c : ℕ × ℕ} :
  c ∈ of_row_lens w hw ↔ ∃ (h : c.fst < w.length), c.snd < w.nth_le c.fst h :=
young_diagram.mem_cells_of_row_lens

/-- The number of rows in `of_row_lens w hw` is the length of `w` -/
lemma row_lens_length_of_row_lens {w : list ℕ} {hw : w.sorted (≥)} (hpos : ∀ x ∈ w, 0 < x) :
  (of_row_lens w hw).row_lens.length = w.length :=
begin
  simp only [length_row_lens, col_len, nat.find_eq_iff, mem_cells, mem_of_row_lens,
             lt_self_iff_false, is_empty.exists_iff, not_not],
  exact ⟨id, λ n hn, ⟨hn, hpos _ (list.nth_le_mem _ _ hn)⟩⟩,
end

/-- The length of the `i`th row in `of_row_lens w hw` is the `i`th entry of `w` -/
lemma row_len_of_row_lens {w : list ℕ} {hw : w.sorted (≥)}
  (i : ℕ) (hi : i < w.length) : (of_row_lens w hw).row_len i = w.nth_le i hi :=
by simp [row_len, nat.find_eq_iff, mem_of_row_lens, hi]

/-- The left_inv direction of the equivalence -/
lemma of_row_lens_to_row_lens_eq_self {μ : young_diagram} :
  of_row_lens _ (row_lens_sorted μ) = μ :=
begin
  ext ⟨i, j⟩,
  simp only [mem_cells, mem_of_row_lens, length_row_lens, nth_le_row_lens],
  simpa [← mem_iff_lt_col_len, mem_iff_lt_row_len] using j.zero_le.trans_lt,
end

/-- The right_inv direction of the equivalence -/
lemma row_lens_of_row_lens_eq_self {w : list ℕ} {hw : w.sorted (≥)} (hpos : ∀ x ∈ w, 0 < x) :
  (of_row_lens w hw).row_lens = w :=
begin
  ext i r,
  cases lt_or_ge i w.length,
  { simp only [option.mem_def, ← list.nth_le_eq_iff, h, row_lens_length_of_row_lens hpos],
    revert r,
    simpa only [eq_iff_eq_cancel_right, nth_le_row_lens] using row_len_of_row_lens _ h },
  { rw [list.nth_eq_none_iff.mpr h, list.nth_eq_none_iff.mpr],
    rwa row_lens_length_of_row_lens hpos }
end

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
def equiv_list_row_lens : young_diagram ≃ {w : list ℕ // w.sorted (≥) ∧ ∀ x ∈ w, 0 < x} :=
{ to_fun    := λ μ, ⟨μ.row_lens, μ.row_lens_sorted, μ.pos_of_mem_row_lens⟩,
  inv_fun   := λ ww, of_row_lens ww.1 ww.2.1,
  left_inv  := λ μ, of_row_lens_to_row_lens_eq_self,
  right_inv := λ ⟨w, hw⟩, subtype.mk_eq_mk.mpr (row_lens_of_row_lens_eq_self hw.2) }

end equiv_list_row_lens

end young_diagram
