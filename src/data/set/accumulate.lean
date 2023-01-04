/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.lattice
/-!
# Accumulate

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/

variables {α β γ : Type*} {s : α → set β} {t : α → set γ}

namespace set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def accumulate [has_le α] (s : α → set β) (x : α) : set β := ⋃ y ≤ x, s y

variable {s}
lemma accumulate_def [has_le α] {x : α} : accumulate s x = ⋃ y ≤ x, s y := rfl
@[simp] lemma mem_accumulate [has_le α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
mem_Union₂

lemma subset_accumulate [preorder α] {x : α} : s x ⊆ accumulate s x :=
λ z, mem_bUnion le_rfl

lemma monotone_accumulate [preorder α] : monotone (accumulate s) :=
λ x y hxy, bUnion_subset_bUnion_left $ λ z hz, le_trans hz hxy

lemma bUnion_accumulate [preorder α] (x : α) : (⋃ y ≤ x, accumulate s y) = ⋃ y ≤ x, s y :=
begin
  apply subset.antisymm,
  { exact Union₂_subset (λ y hy, monotone_accumulate hy) },
  { exact Union₂_mono (λ y hy, subset_accumulate) }
end

lemma Union_accumulate [preorder α] : (⋃ x, accumulate s x) = ⋃ x, s x :=
begin
  apply subset.antisymm,
  { simp only [subset_def, mem_Union, exists_imp_distrib, mem_accumulate],
    intros z x x' hx'x hz, exact ⟨x', hz⟩ },
  { exact Union_mono (λ i, subset_accumulate), }
end

end set
