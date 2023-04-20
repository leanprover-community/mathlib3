/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import logic.encodable.basic
import logic.pairwise

/-!
# Lattice operations on encodable types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/

open set

namespace encodable

variables {α : Type*} {β : Type*} [encodable β]

lemma supr_decode₂ [complete_lattice α] (f : β → α) :
  (⨆ (i : ℕ) (b ∈ decode₂ β i), f b) = (⨆ b, f b) :=
by { rw [supr_comm], simp [mem_decode₂] }

lemma Union_decode₂ (f : β → set α) : (⋃ (i : ℕ) (b ∈ decode₂ β i), f b) = (⋃ b, f b) :=
supr_decode₂ f

@[elab_as_eliminator] lemma Union_decode₂_cases
  {f : β → set α} {C : set α → Prop}
  (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
  C (⋃ b ∈ decode₂ β n, f b) :=
match decode₂ β n with
| none := by { simp, apply H0 }
| (some b) := by { convert H1 b, simp [ext_iff] }
end

theorem Union_decode₂_disjoint_on {f : β → set α} (hd : pairwise (disjoint on f)) :
  pairwise (disjoint on λ i, ⋃ b ∈ decode₂ β i, f b) :=
begin
  rintro i j ij,
  refine disjoint_left.mpr (λ x, _),
  suffices : ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b, by simpa [decode₂_eq_some],
  rintro a rfl ha b rfl hb,
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩
end

end encodable
