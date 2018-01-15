/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order

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

lemma max_lt_iff : max a b < c ↔ (a < c ∧ b < c) :=
⟨assume h, ⟨lt_of_le_of_lt (le_max_left _ _) h, lt_of_le_of_lt (le_max_right _ _) h⟩,
  assume ⟨h₁, h₂⟩, max_lt h₁ h₂⟩

lemma lt_min_iff : a < min b c ↔ (a < b ∧ a < c) :=
⟨assume h, ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩,
  assume ⟨h₁, h₂⟩, lt_min h₁ h₂⟩

lemma lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
⟨assume h, (le_total c b).imp
  (assume hcb, lt_of_lt_of_le h $ max_le (le_refl _) hcb)
  (assume hbc, lt_of_lt_of_le h $ max_le hbc (le_refl _)),
  (assume h, match h with
    | or.inl h := lt_of_lt_of_le h (le_max_left _ _)
    | or.inr h := lt_of_lt_of_le h (le_max_right _ _)
    end)⟩

theorem le_max_left_iff_true (a b : α) : a ≤ max a b ↔ true :=
iff_true_intro (le_max_left a b)

theorem le_max_right_iff_true (a b : α) : b ≤ max a b ↔ true :=
iff_true_intro (le_max_right a b)

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
right_comm min min_comm min_assoc a b c

theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
left_comm max max_comm max_assoc a b c

theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
right_comm max max_comm max_assoc a b c

lemma max_min_distrib_left : max a (min b c) = min (max a b) (max a c) :=
begin
  apply le_antisymm (le_min
    (max_le (le_max_left _ _) (le_trans (min_le_left _ _) (le_max_right _ _)))
    (max_le (le_max_left _ _) (le_trans (min_le_right _ _) (le_max_right _ _)))),
  cases le_total b a with ba ab,
  { rw max_eq_left ba, exact le_trans (min_le_left _ _) (le_max_left _ _) },
  cases le_total c a with ca ac,
  { rw max_eq_left ca, exact le_trans (min_le_right _ _) (le_max_left _ _) },
  rw [max_eq_right ab, max_eq_right ac], apply le_max_right
end

lemma max_min_distrib_right : max (min a b) c = min (max a c) (max b c) :=
by rw [max_comm, max_min_distrib_left, max_comm, max_comm b]

lemma min_max_distrib_left : min a (max b c) = max (min a b) (min a c) :=
begin
  refine le_antisymm _ (max_le
    (le_min (min_le_left _ _) (le_trans (min_le_right _ _) (le_max_left _ _)))
    (le_min (min_le_left _ _) (le_trans (min_le_right _ _) (le_max_right _ _)))),
  cases le_total a b with ab ba,
  { rw min_eq_left ab, exact le_trans (min_le_left _ _) (le_max_left _ _) },
  cases le_total a c with ac ca,
  { rw min_eq_left ac, exact le_trans (min_le_left _ _) (le_max_right _ _) },
  rw [min_eq_right ba, min_eq_right ca], apply min_le_right
end

lemma min_max_distrib_right : min (max a b) c = max (min a c) (min b c) :=
by rw [min_comm, min_max_distrib_left, min_comm, min_comm b]

end

section decidable_linear_ordered_comm_group
variables [decidable_linear_ordered_comm_group α] {a b : α}

attribute [simp] abs_zero abs_neg

def abs_add := @abs_add_le_abs_add_abs

theorem abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
⟨assume h, ⟨neg_le_of_neg_le $ le_trans (neg_le_abs_self _) h, le_trans (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_le_of_le_of_neg_le h₂ $ neg_le_of_neg_le h₁⟩

lemma abs_lt : abs a < b ↔ - b < a ∧ a < b :=
⟨assume h, ⟨neg_lt_of_neg_lt $ lt_of_le_of_lt (neg_le_abs_self _) h, lt_of_le_of_lt (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_lt_of_lt_of_neg_lt h₂ $ neg_lt_of_neg_lt h₁⟩

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
⟨eq_zero_of_abs_eq_zero, λ e, e.symm ▸ abs_zero⟩

lemma abs_pos_iff {a : α} : 0 < abs a ↔ a ≠ 0 :=
⟨λ h, mt abs_eq_zero.2 (ne_of_gt h), abs_pos_of_ne_zero⟩

end decidable_linear_ordered_comm_group

section decidable_linear_ordered_comm_ring
variables [decidable_linear_ordered_comm_ring α] {a b : α}

@[simp] lemma abs_one : abs (1 : α) = 1 := abs_of_pos zero_lt_one

end decidable_linear_ordered_comm_ring
