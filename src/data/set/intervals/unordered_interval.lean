/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import order.bounds

/-!
# Intervals without endpoints ordering

In any decidable linear order `α`, we define the set of elements lying between two elements `a` and
`b` as `Icc (min a b) (max a b)`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `Icc (min a b) (max a b)` is the same as `segment a b`.

## Notation

We use the localized notation `[a, b]` for `interval a b`. One can open the locale `interval` to
make the notation available.

-/

universe u

namespace set

section decidable_linear_order

variables {α : Type u} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ x : α}

/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def interval (a b : α) := Icc (min a b) (max a b)

localized "notation `[`a `, ` b `]` := interval a b" in interval

@[simp] lemma interval_of_le (h : a ≤ b) : [a, b] = Icc a b :=
by rw [interval, min_eq_left h, max_eq_right h]

@[simp] lemma interval_of_ge (h : b ≤ a) : [a, b] = Icc b a :=
by { rw [interval, min_eq_right h, max_eq_left h] }

lemma interval_swap (a b : α) : [a, b] = [b, a] :=
or.elim (le_total a b) (by simp {contextual := tt}) (by simp {contextual := tt})

lemma interval_of_lt (h : a < b) : [a, b] = Icc a b :=
interval_of_le (le_of_lt h)

lemma interval_of_gt (h : b < a) : [a, b] = Icc b a :=
interval_of_ge (le_of_lt h)

lemma interval_of_not_le (h : ¬ a ≤ b) : [a, b] = Icc b a :=
interval_of_gt (lt_of_not_ge h)

lemma interval_of_not_ge (h : ¬ b ≤ a) : [a, b] = Icc a b :=
interval_of_lt (lt_of_not_ge h)

@[simp] lemma interval_self : [a, a] = {a} :=
set.ext $ by simp [le_antisymm_iff, and_comm]

@[simp] lemma nonempty_interval : set.nonempty [a, b] :=
by { simp only [interval, min_le_iff, le_max_iff, nonempty_Icc], left, left, refl }

@[simp] lemma left_mem_interval : a ∈ [a, b] :=
by { rw [interval, mem_Icc], exact ⟨min_le_left _ _, le_max_left _ _⟩ }

@[simp] lemma right_mem_interval : b ∈ [a, b] :=
by { rw interval_swap, exact left_mem_interval }

lemma Icc_subset_interval : Icc a b ⊆ [a, b] :=
by { assume x h, rwa interval_of_le, exact le_trans h.1 h.2 }

lemma Icc_subset_interval' : Icc b a ⊆ [a, b] :=
by { rw interval_swap, apply Icc_subset_interval }

lemma mem_interval_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] :=
Icc_subset_interval ⟨ha, hb⟩

lemma mem_interval_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] :=
Icc_subset_interval' ⟨hb, ha⟩

lemma interval_subset_interval (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
Icc_subset_Icc (le_min h₁.1 h₂.1) (max_le h₁.2 h₂.2)

lemma interval_subset_interval_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
iff.intro (λh, ⟨h left_mem_interval, h right_mem_interval⟩) (λ h, interval_subset_interval h.1 h.2)

lemma interval_subset_interval_iff_le :
  [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
by { rw [interval, interval, Icc_subset_Icc_iff], exact min_le_max }

lemma interval_subset_interval_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] :=
interval_subset_interval h right_mem_interval

lemma interval_subset_interval_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] :=
interval_subset_interval left_mem_interval h

lemma bdd_below_bdd_above_iff_subset_interval (s : set α) :
  bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ [a, b] :=
begin
  rw [bdd_below_bdd_above_iff_subset_Icc],
  split,
  { rintro ⟨a, b, h⟩, exact ⟨a, b, λ x hx, Icc_subset_interval (h hx)⟩ },
  { rintro ⟨a, b, h⟩, exact ⟨min a b, max a b, h⟩ }
end

end decidable_linear_order

open_locale interval

section ordered_add_comm_group

variables {α : Type u} [decidable_linear_ordered_add_comm_group α] {a b x y : α}

/-- If `[x, y]` is a subinterval of `[a, b]`, then the distance between `x` and `y`
is less than or equal to that of `a` and `b` -/
lemma abs_sub_le_of_subinterval (h : [x, y] ⊆ [a, b]) : abs (y - x) ≤ abs (b - a) :=
begin
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs],
  rw [interval_subset_interval_iff_le] at h,
  exact sub_le_sub h.2 h.1,
end

/-- If `x ∈ [a, b]`, then the distance between `a` and `x` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_left_of_mem_interval (h : x ∈ [a, b]) : abs (x - a) ≤ abs (b - a) :=
abs_sub_le_of_subinterval (interval_subset_interval_left h)

/-- If `x ∈ [a, b]`, then the distance between `x` and `b` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_right_of_mem_interval (h : x ∈ [a, b]) : abs (b - x) ≤ abs (b - a) :=
abs_sub_le_of_subinterval (interval_subset_interval_right h)

end ordered_add_comm_group

end set
