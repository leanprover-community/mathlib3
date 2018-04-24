/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Intervals

Nameing conventions:
  `i`: infinite
  `o`: open
  `c`: closed

Each interval has the name `I` + letter for left side + letter for right side

TODO: This is just the beginning a lot of interavals and rules are missing
-/
import data.set.lattice algebra.order algebra.order_functions

namespace set

open set

section intervals
variables {α : Type*} [preorder α]

/-- Left-open right-open interval -/
def Ioo (a b : α) := {x | a < x ∧ x < b}

/-- Left-closed right-open interval -/
def Ico (a b : α) := {x | a ≤ x ∧ x < b}

/-- Left-infinite right-open interval -/
def Iio (a : α) := {x | x < a}

end intervals

section decidable_linear_order
variables {α : Type*} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ : α}

@[simp] lemma Ioo_eq_empty_of_ge {h : b ≤ a} : Ioo a b = ∅ :=
set.ext $ assume x,
  have a < x → b ≤ x, from assume ha, le_trans h $ le_of_lt ha,
  by simp [Ioo]; exact this

lemma Ico_eq_empty_iff : Ico a b = ∅ ↔ (b ≤ a) :=
by rw ← not_lt; exact
⟨assume eq h, have a ∈ Ico a b, from ⟨le_refl a, h⟩, by rwa [eq] at this,
 assume h, eq_empty_iff_forall_not_mem.2 $ assume x ⟨h₁, h₂⟩, h $ lt_of_le_of_lt h₁ h₂⟩

@[simp] lemma Ico_eq_empty : b ≤ a → Ico a b = ∅ := Ico_eq_empty_iff.mpr

lemma Ico_self : Ico a a = ∅ := Ico_eq_empty $ le_refl _

lemma Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ (a₂ ≤ a₁ ∧ b₁ ≤ b₂) :=
⟨assume h,
  have h' : a₁ ∈ Ico a₂ b₂, from h ⟨le_refl _, h₁⟩,
  have ¬ b₂ < b₁, from assume : b₂ < b₁,
    have b₂ ∈ Ico a₂ b₂, from h ⟨le_of_lt h'.right, this⟩,
    lt_irrefl b₂ this.right,
  ⟨h'.left, not_lt.1 $ this⟩,
assume ⟨h₁, h₂⟩ x ⟨hx₁, hx₂⟩, ⟨le_trans h₁ hx₁, lt_of_lt_of_le hx₂ h₂⟩⟩

lemma Ico_subset_Ico_left (h₁ : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
λ c, and.imp_left $ le_trans h₁

lemma Ico_subset_Ico_right (h₁ : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
λ c, and.imp_right $ λ h₂, lt_of_lt_of_le h₂ h₁

lemma Ico_subset_Ioo_left (h₁ : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
λ c, and.imp_left $ lt_of_lt_of_le h₁

lemma Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := λ c, and.imp_left le_of_lt

lemma Ico_subset_Iio_self : Ioo a b ⊆ Iio b := λ c, and.right

lemma Ioo_self : Ioo a a = ∅ := subset_eq_empty Ioo_subset_Ico_self Ico_self

lemma Ico_sdiff_Ioo_eq_singleton (h : a < b) : Ico a b \ Ioo a b = {a} :=
set.ext $ λ c, by simp [Ioo, Ico, -not_lt]; exact
⟨λ ⟨⟨ac, cb⟩, h⟩, ((lt_or_eq_of_le ac).resolve_left $ λ hn, h hn cb).symm,
 λ e, e.symm ▸ ⟨⟨le_refl _, h⟩, (lt_irrefl _).elim⟩⟩

lemma Ico_eq_Ico_iff : Ico a₁ b₁ = Ico a₂ b₂ ↔ ((b₁ ≤ a₁ ∧ b₂ ≤ a₂) ∨ (a₁ = a₂ ∧ b₁ = b₂)) :=
begin
  cases lt_or_le a₁ b₁ with h₁ h₁; cases lt_or_le a₂ b₂ with h₂ h₂,
  { rw [subset.antisymm_iff, Ico_subset_Ico_iff h₁, Ico_subset_Ico_iff h₂],
    simp [iff_def, le_antisymm_iff, or_imp_distrib, not_le_of_gt h₁] {contextual := tt} },
  { rw [Ico_eq_empty_iff.mpr h₂, Ico_eq_empty_iff],
    simp [iff_def, h₂, or_imp_distrib] {contextual := tt} },
  { rw [Ico_eq_empty_iff.mpr h₁, eq_comm, Ico_eq_empty_iff],
    simp [iff_def, h₁, or_imp_distrib] {contextual := tt}, cc },
  { rw [Ico_eq_empty_iff.mpr h₁, Ico_eq_empty_iff.mpr h₂],
    simp [iff_def, h₁, h₂] {contextual := tt} }
end

@[simp] lemma Ico_sdiff_Iio_eq {a b c : α} : Ico a b \ Iio c = Ico (max a c) b :=
set.ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio_eq {a b c : α} : Ico a b ∩ Iio c = Ico a (min b c) :=
set.ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

lemma Ioo_inter_Ioo {a b c d : α} : Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d) :=
set.ext $ by simp [iff_def, Ioo, lt_min_iff, max_lt_iff] {contextual := tt}

end decidable_linear_order

end set