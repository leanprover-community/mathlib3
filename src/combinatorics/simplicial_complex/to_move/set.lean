/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.set.lattice

namespace set

variables {α : Type*} {s t : set α}

lemma disjoint_iff_subset_compl_right :
  disjoint s t ↔ s ⊆ tᶜ :=
disjoint_left

lemma disjoint_iff_subset_compl_left :
  disjoint s t ↔ t ⊆ sᶜ :=
disjoint_right

lemma subset_singleton_iff' (s : set α) (a : α) : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
begin
  obtain (rfl | hs) := s.eq_empty_or_nonempty,
  { simp only [forall_false_left, mem_empty_eq, subset_singleton_iff, implies_true_iff, true_or, eq_self_iff_true]},
  { simp [eq_singleton_iff_nonempty_unique_mem, hs, ne_empty_iff_nonempty.2 hs] }
end

lemma ssubset_singleton_iff_eq_empty (x : α) (X : set α) : X ⊂ {x} ↔ X = ∅ :=
begin
  rw [ssubset_iff_subset_ne, subset_singleton_iff', or_and_distrib_right],
  simp only [or_false, and_iff_left_iff_imp, and_not_self],
  rintro rfl,
  rw [ne_comm, ne_empty_iff_nonempty],
  apply singleton_nonempty,
end

theorem sdiff_union_of_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) :
  (s₂ \ s₁) ∪ s₁ = s₂ :=
set.ext $ λ x, by simpa [em, or_comm, or_and_distrib_left] using or_iff_right_of_imp (@h x)

end set
