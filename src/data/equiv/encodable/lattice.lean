/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
-/
import data.equiv.encodable.basic
import data.finset
import data.set.disjointed
/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/

open set

namespace encodable

variables {α : Type*} {β : Type*} [encodable β]

lemma supr_decode2 [complete_lattice α] (f : β → α) :
  (⨆ (i : ℕ) (b ∈ decode2 β i), f b) = (⨆ b, f b) :=
by { rw [supr_comm], simp [mem_decode2] }

lemma Union_decode2 (f : β → set α) : (⋃ (i : ℕ) (b ∈ decode2 β i), f b) = (⋃ b, f b) :=
supr_decode2 f

@[elab_as_eliminator] lemma Union_decode2_cases
  {f : β → set α} {C : set α → Prop}
  (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
  C (⋃ b ∈ decode2 β n, f b) :=
match decode2 β n with
| none := by { simp, apply H0 }
| (some b) := by { convert H1 b, simp [ext_iff] }
end

theorem Union_decode2_disjoint_on {f : β → set α} (hd : pairwise (disjoint on f)) :
  pairwise (disjoint on λ i, ⋃ b ∈ decode2 β i, f b) :=
begin
  rintro i j ij x ⟨h₁, h₂⟩,
  revert h₁ h₂,
  simp, intros b₁ e₁ h₁ b₂ e₂ h₂,
  refine hd _ _ _ ⟨h₁, h₂⟩,
  cases encodable.mem_decode2.1 e₁,
  cases encodable.mem_decode2.1 e₂,
  exact mt (congr_arg _) ij
end

end encodable

namespace finset

lemma nonempty_encodable {α} (t : finset α) : nonempty $ encodable {i // i ∈ t} :=
begin
  classical, induction t using finset.induction with x t hx ih,
  { refine ⟨⟨λ _, 0, λ _, none, λ ⟨x,y⟩, y.rec _⟩⟩ },
  { cases ih with ih, exactI ⟨encodable.of_equiv _ (finset.subtype_insert_equiv_option hx)⟩ }
end

end finset
