/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import order.partition.equipartition

/-!
# Atomise
-/

open finpartition finset

variables {α : Type*} [decidable_eq α] {s : finset α}

lemma union_of_atoms_aux {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) (i : α) :
  (∃ (B ∈ (atomise s Q).parts), B ⊆ A ∧ i ∈ B) ↔ i ∈ A :=
begin
  split,
  { rintro ⟨B, hB₁, hB₂, hB₃⟩,
    exact hB₂ hB₃ },
  intro hi,
  obtain ⟨B, hB₁, hB₂⟩ := (atomise s Q).exists_mem (hs hi),
  refine ⟨B, hB₁, λ j hj, _, hB₂⟩,
  obtain ⟨P, hP, rfl⟩ := (mem_atomise.1 hB₁).2,
  simp only [mem_filter] at hB₂ hj,
  rwa [←hj.2 _ hA, hB₂.2 _ hA]
end

open_locale classical

lemma union_of_atoms' {Q : finset (finset α)} (A : finset α) (hx : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter $ λ B, B ⊆ A ∧ B.nonempty).bUnion id = A :=
begin
  ext x,
  simp only [mem_bUnion, exists_prop, mem_filter, id.def, and_assoc],
  rw ←union_of_atoms_aux hx hs,
  simp only [exists_prop, finset.nonempty],
  tauto,
end

lemma partial_atomise {Q : finset (finset α)} (A : finset α) (hA : A ∈ Q) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).card ≤ 2^(Q.card - 1) :=
begin
  suffices h :
    (atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty) ⊆
      (Q.erase A).powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ insert A P ↔ i ∈ x)),
  { refine (card_le_of_subset h).trans (card_image_le.trans _),
    rw [card_powerset, card_erase_of_mem hA] },
  rw subset_iff,
  simp only [mem_erase, mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc,
    finset.nonempty, exists_imp_distrib, and_imp, mem_atomise, forall_apply_eq_imp_iff₂],
  rintro P' i hi P PQ rfl hy₂ j hj,
  refine ⟨P.erase A, erase_subset_erase _ PQ, _⟩,
  have : A ∈ P,
  { rw mem_filter at hi,
    rw hi.2 _ hA,
    exact hy₂ (mem_filter.2 hi) },
  simp only [insert_erase this, filter_congr_decidable],
end
