/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import data.finset.intervals
import data.set.finite

/-!
# Sup-closed sets

Properties of sets `s` such that for `x, y ∈ s`, `x ⊔ y ∈ s`.

-/

namespace set

/-- A set `s` is sup-closed if for all `x₁, x₂ ∈ s`, `x₁ ⊔ x₂ ∈ s`. -/
def sup_closed {α} [has_sup α] (s : set α) : Prop := ∀ x1 x2, x1 ∈ s → x2 ∈ s → x1 ⊔ x2 ∈ s

lemma sup_closed_empty {α} [has_sup α] : sup_closed (∅ : set α) := by simp [sup_closed]

lemma sup_closed_univ {α} [has_sup α] : sup_closed (univ : set α) := by simp [sup_closed]

lemma sup_closed.inter {α} [has_sup α] {s t : set α} (hs : sup_closed s) (ht : sup_closed t) :
  sup_closed (s ∩ t) :=
begin
  intros x y hx hy,
  rw mem_inter_iff at hx hy,
  exact mem_inter (hs x y hx.left hy.left) (ht x y hx.right hy.right),
end

lemma sup_closed_singleton {α} [semilattice_sup α] (x : α) : sup_closed ({x} : set α) :=
λ _ _ y1_mem y2_mem, by { rw set.mem_singleton_iff at *, rw [y1_mem, y2_mem, sup_idem], }

lemma sup_closed_of_linearly_ordered {α} [semilattice_sup α] {s : set α}
  (hs : ∀ x y, x ∈ s → y ∈ s → x ≤ y ∨ y ≤ x) :
  sup_closed s :=
begin
  intros x y hx hy,
  cases hs x y hx hy with h_x_le h_y_le,
  { rwa sup_eq_right.mpr h_x_le, },
  { rwa sup_eq_left.mpr h_y_le, },
end

lemma sup_closed_of_linear_order {α} [complete_linear_order α] (s : set α) : sup_closed s :=
sup_closed_of_linearly_ordered (λ x y _ _, le_total x y)

lemma sup_closed_generate_from_set {α} [boolean_algebra α] (s : α) :
  sup_closed ({⊥, ⊤, s, sᶜ} : set α) :=
begin
  intros a b ha hb,
  simp only [mem_singleton_iff, mem_insert_iff] at ha hb ⊢,
  cases ha, { simp [ha, hb], },
  cases hb, { simp [ha, hb], },
  cases ha, { simp [ha, hb], },
  cases hb, { simp [ha, hb], },
  cases ha; cases hb; simp [ha, hb],
end

section nat_function
variables {α : Type*} [complete_lattice α]

lemma bsupr_le_mem_of_sup_closed {s : set α} (hs : sup_closed s) (f : ℕ → α) (hfs : ∀ i, f i ∈ s)
  (m : ℕ) :
  (⨆ i ≤ m, f i) ∈ s :=
begin
  induction m with m hm,
  { simp [hfs 0], },
  { rw bsupr_nat_succ,
    exact hs _ _ hm (hfs m.succ), },
end

lemma supr_mem_of_sup_closed_of_finite {s : set α} (hs : sup_closed s) (hfin : finite s)
  (f : ℕ → α) (hfs : ∀ i, f i ∈ s) :
  (⨆ i, f i) ∈ s :=
begin
  obtain ⟨m, h⟩ := supr_eq_bsupr_le_of_finite hfin f (λ i, or.inl (hfs i)),
  rw h,
  exact bsupr_le_mem_of_sup_closed hs f hfs m,
end

end nat_function

section useful_examples

lemma sup_closed_finset_Ico_right (N : ℕ) :
  sup_closed {s : finset ℕ | ∃ r : ℕ, s = finset.Ico N (N+r+1)} :=
begin
  refine sup_closed_of_linearly_ordered _,
  rintros s1 s2 ⟨r1, hs1⟩ ⟨r2, hs2⟩,
  rw [hs1, hs2],
  cases le_total r1 r2,
  { exact or.inl (finset.Ico.subset le_rfl (by simp [h])), },
  { exact or.inr (finset.Ico.subset le_rfl (by simp [h])), },
end

end useful_examples

end set
