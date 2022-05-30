/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.finset.basic

/-!
# To move
-/

namespace finset
variables {α β : Type*} [decidable_eq α] [decidable_eq β] {s t : finset α}

lemma erase_image_subset_image_erase  (f : α → β) (s : finset α) (a : α) :
  (s.image f).erase (f a) ⊆ (s.erase a).image f :=
begin
  intro b,
  simp only [and_imp, exists_prop, finset.mem_image, exists_imp_distrib, finset.mem_erase],
  rintro hb x hx rfl,
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩,
end

lemma subset_iff_eq_or_ssubset {s t : finset α} : s ⊆ t ↔ s = t ∨ s ⊂ t :=
begin
  refine ⟨eq_or_ssubset_of_subset, _⟩,
  rintro (rfl | ss),
  { refl },
  { exact ss.1 }
end

@[simp] lemma disjoint_coe : disjoint (s : set α) (t : set α) ↔ disjoint s t :=
by { rw [finset.disjoint_left, set.disjoint_left], refl }

end finset
