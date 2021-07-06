/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.list.basic

lemma list.exists_min {α : Type*} [semilattice_inf α] :
  ∀ {s : list α} (hs₁ : s ≠ []), ∃ z, ∀ y ∈ s, z ≤ y
| [] h := (h rfl).elim
| [x] h := ⟨x, by simp⟩
| (x :: y :: ys) _ :=
  begin
    rcases list.exists_min (list.cons_ne_nil y ys) with ⟨t, ht⟩,
    refine ⟨t ⊓ x, _⟩,
    rintro z (rfl | rfl | hz),
    { apply inf_le_right },
    { apply le_trans inf_le_left (ht z (list.mem_cons_self z ys)) },
    { apply le_trans inf_le_left (ht z (list.mem_cons_of_mem _ hz)) }
  end

lemma list.exists_min_of_inf_closed {α : Type*} [semilattice_inf α] {s : list α}
  (hs₁ : s ≠ []) (hs₂ : ∀ x y ∈ s, x ⊓ y ∈ s) :
  ∃ z ∈ s, ∀ y ∈ s, z ≤ y :=
begin
  have hs'₁ : s.attach ≠ [] := by simpa using hs₁,
  letI : semilattice_inf {y // y ∈ s} := subtype.semilattice_inf (λ x y hx hy, hs₂ x y hx hy),
  rcases list.exists_min hs'₁ with ⟨⟨x, hx₁⟩, hx₂⟩,
  refine ⟨x, hx₁, λ y hy, hx₂ ⟨y, hy⟩ _⟩,
  simp only [list.mem_attach],
end
