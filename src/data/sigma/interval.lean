/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.order
import order.locally_finite

/-!
# Finite intervals in a sigma type

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

open function

section ite
variables {α β γ : Sort*} {σ : α → Sort*} (f : α → β) {P Q : Prop} [decidable P] [decidable Q]
  {a b c : α} {A : P → α} {B : ¬ P → α}

@[simp] lemma dite_eq_right_iff : dite P A (λ _, b) = b ↔ ∀ h, A h = b := sorry
lemma dite_ne_right_iff : dite P A (λ _, b) ≠ b ↔ ∃ h, A h ≠ b := sorry

end ite

namespace finset
variables {α β : Type*} {f : α ↪ β} {s : finset α}

lemma map_nonempty : (s.map f).nonempty ↔ s.nonempty :=
by rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, ne.def, map_eq_empty]

end finset

namespace finset
variables {ι : Type*} {α : ι → Type*} [decidable_eq ι]

/-- Lifts maps `α i → α i → finset (α i)` to a map `Σ i, α i → Σ i, α i → finset (Σ i, α i)`. -/
def sigma_lift (f : Π ⦃i⦄, α i → α i → finset (α i)) (a b : Σ i, α i) : finset (Σ i, α i) :=
dite (a.1 = b.1) (λ h, (f (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅)

lemma mem_sigma_lift (f : Π ⦃i⦄, α i → α i → finset (α i)) (a b x : Σ i, α i) :
  x ∈ sigma_lift f a b ↔ ∃ (ha : a.1 = x.1) (hb : b.1 = x.1), x.2 ∈ f (ha.rec a.2) (hb.rec b.2) :=
begin
  obtain ⟨⟨i, a⟩, j, b⟩ := ⟨a, b⟩,
  obtain rfl | h := decidable.eq_or_ne i j,
  { split,
    { simp_rw [sigma_lift, dif_pos rfl, mem_map, embedding.sigma_mk_apply],
      rintro ⟨x, hx, rfl⟩,
      exact ⟨rfl, rfl, hx⟩ },
    { rintro ⟨⟨⟩, ⟨⟩, hx⟩,
      rw [sigma_lift, dif_pos rfl, mem_map],
      exact ⟨_, hx, by simp [sigma.ext_iff]⟩ } },
  { rw [sigma_lift, dif_neg h],
    refine iff_of_false (not_mem_empty _) _,
    rintro ⟨⟨⟩, ⟨⟩, _⟩,
    exact h rfl }
end

variables {f g : Π ⦃i⦄, α i → α i → finset (α i)} {a b : Σ i, α i}

lemma sigma_lift_nonempty :
  (sigma_lift f a b).nonempty ↔ ∃ h : a.1 = b.1, (f (h.rec a.2) b.2).nonempty :=
begin
  simp_rw nonempty_iff_ne_empty,
  convert dite_ne_right_iff,
  ext h,
  simp_rw [←nonempty_iff_ne_empty],
  exact map_nonempty.symm,
end

lemma sigma_lift_eq_empty : (sigma_lift f a b) = ∅ ↔ ∀ h : a.1 = b.1, (f (h.rec a.2) b.2) = ∅ :=
begin
  convert dite_eq_right_iff,
  exact forall_congr_eq (λ h, propext map_eq_empty.symm),
end

lemma sigma_lift_mono (h : ∀ ⦃i⦄ ⦃a b : α i⦄, f a b ⊆ g a b) (a b : Σ i, α i) :
  sigma_lift f a b ⊆ sigma_lift g a b :=
begin
  rintro x hx,
  rw mem_sigma_lift at ⊢ hx,
  obtain ⟨ha, hb, hx⟩ := hx,
  exact ⟨ha, hb, h hx⟩,
end

variables (f a b)

lemma card_sigma_lift :
  (sigma_lift f a b).card = dite (a.1 = b.1) (λ h, (f (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

end finset

open finset function

namespace sigma
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [decidable_eq ι] [Π i, preorder (α i)] [Π i, locally_finite_order (α i)]

instance : locally_finite_order (Σ i, α i) :=
{ finset_Icc := sigma_lift (λ _, Icc),
  finset_Ico := sigma_lift (λ _, Ico),
  finset_Ioc := sigma_lift (λ _, Ioc),
  finset_Ioo := sigma_lift (λ _, Ioo),
  finset_mem_Icc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ico := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioo := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end }

section
variables (a b : Σ i, α i)

@[simp] lemma card_Icc : (Icc a b).card = dite (a.1 = b.1)
    (λ h, (Icc (h.rec a.2) b.2).card) (λ _, 0) :=
card_sigma_lift _ _ _

@[simp] lemma card_Ico : (Ico a b).card = dite (a.1 = b.1)
    (λ h, (Ico (h.rec a.2) b.2).card) (λ _, 0) :=
card_sigma_lift _ _ _

@[simp] lemma card_Ioc : (Ioc a b).card = dite (a.1 = b.1)
    (λ h, (Ioc (h.rec a.2) b.2).card) (λ _, 0) :=
card_sigma_lift _ _ _

@[simp] lemma card_Ioo : (Ioo a b).card = dite (a.1 = b.1)
    (λ h, (Ioo (h.rec a.2) b.2).card) (λ _, 0) :=
card_sigma_lift _ _ _

end

variables (i : ι) (a b : α i)

@[simp] lemma card_Icc_mk_mk : (Icc (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Icc a b).card :=
by rw [card_Icc, dif_pos rfl]

@[simp] lemma card_Ico_mk_mk : (Ico (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ico a b).card :=
by rw [card_Ico, dif_pos rfl]

@[simp] lemma card_Ioc_mk_mk : (Ioc (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ioc a b).card :=
by rw [card_Ioc, dif_pos rfl]

@[simp] lemma card_Ioo_mk_mk : (Ioo (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ioo a b).card :=
by rw [card_Ioo, dif_pos rfl]

end disjoint
end sigma
