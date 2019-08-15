/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Intervals

Naming conventions:
  `i`: infinite
  `o`: open
  `c`: closed

Each interval has the name `I` + letter for left side + letter for right side

TODO: This is just the beginning; a lot of rules are missing
-/
import algebra.order algebra.order_functions data.set.lattice
import tactic.tauto

namespace set

open set

section intervals
variables {α : Type*} [preorder α] {a a₁ a₂ b b₁ b₂ x : α}

/-- Left-open right-open interval -/
def Ioo (a b : α) := {x | a < x ∧ x < b}

/-- Left-closed right-open interval -/
def Ico (a b : α) := {x | a ≤ x ∧ x < b}

/-- Left-infinite right-open interval -/
def Iio (a : α) := {x | x < a}

/-- Left-closed right-closed interval -/
def Icc (a b : α) := {x | a ≤ x ∧ x ≤ b}

/-- Left-infinite right-closed interval -/
def Iic (b : α) := {x | x ≤ b}

/-- Left-open right-closed interval -/
def Ioc (a b : α) := {x | a < x ∧ x ≤ b}

/-- Left-closed right-infinite interval -/
def Ici (a : α) := {x | a ≤ x}

/-- Left-open right-infinite interval -/
def Ioi (a : α) := {x | a < x}

@[simp] lemma mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := iff.rfl
@[simp] lemma mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := iff.rfl
@[simp] lemma mem_Iio : x ∈ Iio b ↔ x < b := iff.rfl
@[simp] lemma mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := iff.rfl
@[simp] lemma mem_Iic : x ∈ Iic b ↔ x ≤ b := iff.rfl
@[simp] lemma mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := iff.rfl
@[simp] lemma mem_Ici : x ∈ Ici a ↔ a ≤ x := iff.rfl
@[simp] lemma mem_Ioi : x ∈ Ioi a ↔ a < x := iff.rfl

@[simp] lemma left_mem_Ioo : a ∈ Ioo a b ↔ false := ⟨λ h, lt_irrefl a h.1, λ h, false.elim h⟩
@[simp] lemma left_mem_Ico : a ∈ Ico a b ↔ a < b := ⟨λ h, h.2, λ h, ⟨le_refl _, h⟩⟩
@[simp] lemma left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := ⟨λ h, h.2, λ h, ⟨le_refl _, h⟩⟩
@[simp] lemma left_mem_Ioc : a ∈ Ioc a b ↔ false := ⟨λ h, lt_irrefl a h.1, λ h, false.elim h⟩
@[simp] lemma right_mem_Ioo : b ∈ Ioo a b ↔ false := ⟨λ h, lt_irrefl b h.2, λ h, false.elim h⟩
@[simp] lemma right_mem_Ico : b ∈ Ico a b ↔ false := ⟨λ h, lt_irrefl b h.2, λ h, false.elim h⟩
@[simp] lemma right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := ⟨λ h, h.1, λ h, ⟨h, le_refl _⟩⟩
@[simp] lemma right_mem_Ioc : b ∈ Ioc a b ↔ a < b := ⟨λ h, h.1, λ h, ⟨h, le_refl _⟩⟩

@[simp] lemma Ioo_eq_empty (h : b ≤ a) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨h₁, h₂⟩, not_le_of_lt (lt_trans h₁ h₂) h

@[simp] lemma Ico_eq_empty (h : b ≤ a) : Ico a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨h₁, h₂⟩, not_le_of_lt (lt_of_le_of_lt h₁ h₂) h

@[simp] lemma Icc_eq_empty (h : b < a) : Icc a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨h₁, h₂⟩, not_lt_of_le (le_trans h₁ h₂) h

@[simp] lemma Ioc_eq_empty (h : b ≤ a) : Ioc a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨h₁, h₂⟩, not_lt_of_le (le_trans h₂ h) h₁

@[simp] lemma Ioo_self (a : α) : Ioo a a = ∅ := Ioo_eq_empty $ le_refl _
@[simp] lemma Ico_self (a : α) : Ico a a = ∅ := Ico_eq_empty $ le_refl _
@[simp] lemma Ioc_self (a : α) : Ioc a a = ∅ := Ioc_eq_empty $ le_refl _

lemma Iio_ne_empty [no_bot_order α] (a : α) : Iio a ≠ ∅ :=
ne_empty_iff_exists_mem.2 (no_bot a)

lemma Ioi_ne_empty [no_top_order α] (a : α) : Ioi a ≠ ∅ :=
ne_empty_iff_exists_mem.2 (no_top a)

lemma Iic_ne_empty (b : α) : Iic b ≠ ∅ :=
ne_empty_iff_exists_mem.2 ⟨b, le_refl b⟩

lemma Ici_ne_empty (a : α) : Ici a ≠ ∅ :=
ne_empty_iff_exists_mem.2 ⟨a, le_refl a⟩

lemma Ioo_subset_Ioo (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ioo a₁ b₁ ⊆ Ioo a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨lt_of_le_of_lt h₁ hx₁, lt_of_lt_of_le hx₂ h₂⟩

lemma Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
Ioo_subset_Ioo h (le_refl _)

lemma Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
Ioo_subset_Ioo (le_refl _) h

lemma Ico_subset_Ico (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨le_trans h₁ hx₁, lt_of_lt_of_le hx₂ h₂⟩

lemma Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
Ico_subset_Ico h (le_refl _)

lemma Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
Ico_subset_Ico (le_refl _) h

lemma Icc_subset_Icc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Icc a₁ b₁ ⊆ Icc a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨le_trans h₁ hx₁, le_trans hx₂ h₂⟩

lemma Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
Icc_subset_Icc h (le_refl _)

lemma Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
Icc_subset_Icc (le_refl _) h

lemma Ioc_subset_Ioc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ioc a₁ b₁ ⊆ Ioc a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨lt_of_le_of_lt h₁ hx₁, le_trans hx₂ h₂⟩

lemma Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
Ioc_subset_Ioc h (le_refl _)

lemma Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
Ioc_subset_Ioc (le_refl _) h

lemma Ico_subset_Ioo_left (h₁ : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
λ x, and.imp_left $ lt_of_lt_of_le h₁

lemma Icc_subset_Ico_right (h₁ : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ :=
λ x, and.imp_right $ λ h₂, lt_of_le_of_lt h₂ h₁

lemma Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := λ x, and.imp_left le_of_lt

lemma Ico_subset_Icc_self : Ico a b ⊆ Icc a b := λ x, and.imp_right le_of_lt

lemma Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

lemma Ico_subset_Iio_self : Ioo a b ⊆ Iio b := λ x, and.right

lemma Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, ⟨(h ⟨le_refl _, h₁⟩).1, (h ⟨h₁, le_refl _⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨le_trans h hx, le_trans hx' h'⟩⟩

lemma Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
⟨λ h, ⟨(h ⟨le_refl _, h₁⟩).1, (h ⟨h₁, le_refl _⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨lt_of_lt_of_le h hx, lt_of_le_of_lt hx' h'⟩⟩

lemma Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
⟨λ h, ⟨(h ⟨le_refl _, h₁⟩).1, (h ⟨h₁, le_refl _⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨le_trans h hx, lt_of_le_of_lt hx' h'⟩⟩

lemma Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, ⟨(h ⟨le_refl _, h₁⟩).1, (h ⟨h₁, le_refl _⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨lt_of_lt_of_le h hx, le_trans hx' h'⟩⟩

lemma Icc_subset_Iio_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Iio b₂ ↔ b₁ < b₂ :=
⟨λ h, h ⟨h₁, le_refl _⟩, λ h x ⟨hx, hx'⟩, lt_of_le_of_lt hx' h⟩

lemma Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ :=
⟨λ h, h ⟨le_refl _, h₁⟩, λ h x ⟨hx, hx'⟩, lt_of_lt_of_le h hx⟩

lemma Icc_subset_Iic_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Iic b₂ ↔ b₁ ≤ b₂ :=
⟨λ h, h ⟨h₁, le_refl _⟩, λ h x ⟨hx, hx'⟩, le_trans hx' h⟩

lemma Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ :=
⟨λ h, h ⟨le_refl _, h₁⟩, λ h x ⟨hx, hx'⟩, le_trans h hx⟩
end intervals

section partial_order
variables {α : Type*} [partial_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
set.ext $ by simp [Icc, le_antisymm_iff, and_comm]

lemma Ico_diff_Ioo_eq_singleton (h : a < b) : Ico a b \ Ioo a b = {a} :=
set.ext $ λ x, begin
  simp, split,
  { rintro ⟨⟨ax, xb⟩, h⟩,
    exact eq.symm (classical.by_contradiction
      (λ ne, h (lt_of_le_of_ne ax ne) xb)) },
  { rintro rfl, exact ⟨⟨le_refl _, h⟩, (lt_irrefl x).elim⟩ }
end

lemma Icc_diff_Ico_eq_singleton (h : a ≤ b) : Icc a b \ Ico a b = {b} :=
set.ext $ λ x, begin
  simp, split,
  { rintro ⟨⟨ax, xb⟩, h⟩,
    exact classical.by_contradiction
      (λ ne, h ax (lt_of_le_of_ne xb ne)) },
  { rintro rfl, exact ⟨⟨h, le_refl _⟩, λ _, lt_irrefl x⟩ }
end

end partial_order

section linear_order
variables {α : Type*} [linear_order α] {a a₁ a₂ b b₁ b₂ : α}

lemma Ioo_eq_empty_iff [densely_ordered α] : Ioo a b = ∅ ↔ b ≤ a :=
⟨λ eq, le_of_not_lt $ λ h,
  let ⟨x, h₁, h₂⟩ := dense h in
  eq_empty_iff_forall_not_mem.1 eq x ⟨h₁, h₂⟩,
Ioo_eq_empty⟩

lemma Ico_eq_empty_iff : Ico a b = ∅ ↔ b ≤ a :=
⟨λ eq, le_of_not_lt $ λ h, eq_empty_iff_forall_not_mem.1 eq a ⟨le_refl _, h⟩,
 Ico_eq_empty⟩

lemma Icc_eq_empty_iff : Icc a b = ∅ ↔ b < a :=
⟨λ eq, lt_of_not_ge $ λ h, eq_empty_iff_forall_not_mem.1 eq a ⟨le_refl _, h⟩,
 Icc_eq_empty⟩

lemma Ico_subset_Ico_iff (h₁ : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, have a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_refl _, h₁⟩,
  ⟨this.1, le_of_not_lt $ λ h', lt_irrefl b₂ (h ⟨le_of_lt this.2, h'⟩).2⟩,
 λ ⟨h₁, h₂⟩, Ico_subset_Ico h₁ h₂⟩

lemma Ioo_subset_Ioo_iff [densely_ordered α] (h₁ : a₁ < b₁) :
  Ioo a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, begin
  rcases dense h₁ with ⟨x, xa, xb⟩,
  split; refine le_of_not_lt (λ h', _),
  { have ab := lt_trans (h ⟨xa, xb⟩).1 xb,
    exact lt_irrefl _ (h ⟨h', ab⟩).1 },
  { have ab := lt_trans xa (h ⟨xa, xb⟩).2,
    exact lt_irrefl _ (h ⟨ab, h'⟩).2 }
end, λ ⟨h₁, h₂⟩, Ioo_subset_Ioo h₁ h₂⟩

lemma Ico_eq_Ico_iff (h : a₁ < b₁ ∨ a₂ < b₂) : Ico a₁ b₁ = Ico a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
⟨λ e, begin
  simp [subset.antisymm_iff] at e, simp [le_antisymm_iff],
  cases h; simp [Ico_subset_Ico_iff h] at e;
    [ rcases e with ⟨⟨h₁, h₂⟩, e'⟩, rcases e with ⟨e', ⟨h₁, h₂⟩⟩ ];
    have := (Ico_subset_Ico_iff (lt_of_le_of_lt h₁ $ lt_of_lt_of_le h h₂)).1 e';
    tauto
end, λ ⟨h₁, h₂⟩, by rw [h₁, h₂]⟩

end linear_order

section decidable_linear_order
variables {α : Type*} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ : α}

@[simp] lemma Ico_diff_Iio {a b c : α} : Ico a b \ Iio c = Ico (max a c) b :=
set.ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio {a b c : α} : Ico a b ∩ Iio c = Ico a (min b c) :=
set.ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

lemma Ioo_inter_Ioo {a b c d : α} : Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d) :=
set.ext $ by simp [iff_def, Ioo, lt_min_iff, max_lt_iff] {contextual := tt}

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
lemma eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α}
  (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (hy : y₁ < y₂) (h2 : x₂ ∈ Ico y₁ y₂) :
  y₁ = x₂ :=
begin
  apply le_antisymm h2.1, rw [←not_lt], intro h3,
  apply not_disjoint_iff.mpr ⟨max y₁ x₁, _, _⟩ h,
  simp [le_refl, h3, hx],
  simp [le_refl, hy, lt_trans hx h2.2]
end

end decidable_linear_order

section ordered_comm_group

variables {α : Type*} [ordered_comm_group α]

lemma image_neg_Iio (r : α) : image (λz, -z) (Iio r) = Ioi (-r) :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp only [mem_Ioi, neg_lt_neg_iff],
    exact hz'.1 },
  { intros hz,
    simp only [mem_image, mem_Iio],
    use -z,
    simp [hz],
    exact neg_lt.1 hz }
end

lemma image_neg_Iic (r : α)  : image (λz, -z) (Iic r) = Ici (-r) :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp only [neg_le_neg_iff, mem_Ici],
    exact hz'.1 },
  { intros hz,
    simp only [mem_image, mem_Iic],
    use -z,
    simp [hz],
    exact neg_le.1 hz }
end

end ordered_comm_group

section decidable_linear_ordered_comm_group

variables {α : Type*} [decidable_linear_ordered_comm_group α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
lemma nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
  nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp* },
  { use max x (x + dy), simp [*, le_refl] }
end

end decidable_linear_ordered_comm_group

end set
