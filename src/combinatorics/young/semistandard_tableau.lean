/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import combinatorics.young.young_diagram

/-!
# Semistandard Young tableaux

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A semistandard Young tableau is a filling of a Young diagram by natural numbers, such that
the entries are weakly increasing left-to-right along rows (i.e. for fixed `i`), and
strictly-increasing top-to-bottom along columns (i.e. for fixed `j`).

An example of an SSYT of shape `μ = [4, 2, 1]` is:

```text
0 0 0 2
1 1
2
```

We represent an SSYT as a function `ℕ → ℕ → ℕ`, which is required to be zero for all pairs
`(i, j) ∉ μ` and to satisfy the row-weak and column-strict conditions on `μ`.


## Main definitions

- `ssyt (μ : young_diagram)` : semistandard Young tableaux of shape `μ`. There is
  a `has_coe_to_fun` instance such that `T i j` is value of the `(i, j)` entry of the SSYT `T`.
- `ssyt.highest_weight (μ : young_diagram)`: the semistandard Young tableau whose `i`th row
  consists entirely of `i`s, for each `i`.

## Tags

Semistandard Young tableau

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

/-- A semistandard Young tableau (SSYT) is a filling of the cells of a Young diagram by natural
numbers, such that the entries in each row are weakly increasing (left to right), and the entries
in each column are strictly increasing (top to bottom).

Here, an SSYT is represented as an unrestricted function `ℕ → ℕ → ℕ` that, for reasons
of extensionality, is required to vanish outside `μ`. -/
structure ssyt (μ : young_diagram) :=
(entry : ℕ → ℕ → ℕ)
(row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2)
(col_strict' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j)
(zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0)

namespace ssyt

instance fun_like {μ : young_diagram} : fun_like (ssyt μ) ℕ (λ _, ℕ → ℕ) :=
{ coe := ssyt.entry,
  coe_injective' := λ T T' h, by { cases T, cases T', congr' } }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance {μ : young_diagram} : has_coe_to_fun (ssyt μ) (λ _, ℕ → ℕ → ℕ) :=
fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {μ : young_diagram} {T : ssyt μ} : T.entry = (T : ℕ → ℕ → ℕ) := rfl

@[ext] theorem ext {μ : young_diagram} {T T' : ssyt μ} (h : ∀ i j, T i j = T' i j) : T = T' :=
fun_like.ext T T' (λ x, by { funext, apply h })

/-- Copy of an `ssyt μ` with a new `entry` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy {μ : young_diagram} (T : ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) :
  ssyt μ :=
{ entry := entry',
  row_weak' := λ _ _ _, h.symm ▸ T.row_weak',
  col_strict' := λ _ _ _, h.symm ▸ T.col_strict',
  zeros' := λ _ _, h.symm ▸ T.zeros' }

@[simp] lemma coe_copy {μ : young_diagram} (T : ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) :
  ⇑(T.copy entry' h) = entry' :=
rfl

lemma copy_eq {μ : young_diagram} (T : ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) :
  T.copy entry' h = T :=
fun_like.ext' h

lemma row_weak {μ : young_diagram} (T : ssyt μ) {i j1 j2 : ℕ}
  (hj : j1 < j2) (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
T.row_weak' hj hcell

lemma col_strict {μ : young_diagram} (T : ssyt μ) {i1 i2 j : ℕ}
  (hi : i1 < i2) (hcell : (i2, j) ∈ μ) : T i1 j < T i2 j :=
T.col_strict' hi hcell

lemma zeros {μ : young_diagram} (T : ssyt μ)
  {i j : ℕ} (not_cell : (i, j) ∉ μ) : T i j = 0 := T.zeros' not_cell

lemma row_weak_of_le {μ : young_diagram} (T : ssyt μ) {i j1 j2 : ℕ}
  (hj : j1 ≤ j2) (cell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
by { cases eq_or_lt_of_le hj, subst h, exact T.row_weak h cell }

lemma col_weak {μ : young_diagram} (T : ssyt μ) {i1 i2 j : ℕ}
  (hi : i1 ≤ i2) (cell : (i2, j) ∈ μ) : T i1 j ≤ T i2 j :=
by { cases eq_or_lt_of_le hi, subst h, exact le_of_lt (T.col_strict h cell) }

/-- The "highest weight" SSYT of a given shape is has all i's in row i, for each i. -/
def highest_weight (μ : young_diagram) : ssyt μ :=
{ entry := λ i j, if (i, j) ∈ μ then i else 0,
  row_weak' := λ i j1 j2 hj hcell,
    by rw [if_pos hcell, if_pos (μ.up_left_mem (by refl) (le_of_lt hj) hcell)],
  col_strict' := λ i1 i2 j hi hcell,
    by rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by refl) hcell)],
  zeros' := λ i j not_cell, if_neg not_cell }

@[simp] lemma highest_weight_apply {μ : young_diagram} {i j : ℕ} :
  highest_weight μ i j = if (i, j) ∈ μ then i else 0 := rfl

instance {μ : young_diagram} : inhabited (ssyt μ) := ⟨ssyt.highest_weight μ⟩

end ssyt
