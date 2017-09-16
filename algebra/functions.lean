/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

universe u
variables {α : Type u}

section
variables [decidable_linear_order α] {a b c : α}

lemma le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
⟨λ h, ⟨le_trans h (min_le_left a b), le_trans h (min_le_right a b)⟩,
 λ ⟨h₁, h₂⟩, le_min h₁ h₂⟩

lemma max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
⟨λ h, ⟨le_trans (le_max_left a b) h, le_trans (le_max_right a b) h⟩,
 λ ⟨h₁, h₂⟩, max_le h₁ h₂⟩

end

section decidable_linear_ordered_comm_group
variables [decidable_linear_ordered_comm_group α] {a b : α}

theorem abs_le : abs a ≤ b ↔ (- b ≤ a ∧ a ≤ b) :=
⟨assume h, ⟨neg_le_of_neg_le $ le_trans (neg_le_abs_self _) h, le_trans (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_le_of_le_of_neg_le h₂ $ neg_le_of_neg_le h₁⟩

lemma abs_lt : abs a < b ↔ (- b < a ∧ a < b) :=
⟨assume h, ⟨neg_lt_of_neg_lt $ lt_of_le_of_lt (neg_le_abs_self _) h, lt_of_le_of_lt (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_lt_of_lt_of_neg_lt h₂ $ neg_lt_of_neg_lt h₁⟩

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
⟨eq_zero_of_abs_eq_zero, λ e, e.symm ▸ abs_zero⟩

end decidable_linear_ordered_comm_group
