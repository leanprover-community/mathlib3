/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import data.set.intervals

/-!
# Intervals

`a..b` is the set of elements lying between `a` and `b`, with both endpoints included.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. This
version of interval is always the set of things lying between `a` and `b`, regardless of the
relative order of `a` and `b`.
-/

universe u

namespace set

section decidable_linear_order

variables {α : Type u} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ x : α}

/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def interval (a b : α) := if a ≤ b then Icc a b else Icc b a

localized "infix `..`:1025 := interval" in interval

@[simp] lemma interval_of_le (h : a ≤ b) : a..b = Icc a b :=
if_pos h

@[simp] lemma interval_of_le' (h : b ≤ a) : a..b = Icc b a :=
by { rw interval, split_ifs with h', { rw le_antisymm h h' }, refl }

lemma interval_swap (a b : α) : a..b = b..a :=
or.elim (le_total a b) (by simp {contextual := tt}) (by simp {contextual := tt})

lemma interval_of_lt (h : a < b) : a..b = Icc a b :=
interval_of_le (le_of_lt h)

lemma interval_of_lt' (h : b < a) : a..b = Icc b a :=
interval_of_le' (le_of_lt h)

lemma interval_of_not_le (h : ¬ a ≤ b) : a..b = Icc b a :=
if_neg h

lemma interval_of_not_le' (h : ¬ b ≤ a) : a..b = Icc a b :=
by { rw interval_swap, exact if_neg h }

@[simp] lemma interval_self : a..a = {a} :=
set.ext $ by simp [le_antisymm_iff, and_comm]

@[simp] lemma nonempty_interval : set.nonempty a..b :=
by { rw interval, split_ifs, { simp [h] }, simp [le_of_not_le h] }

@[simp] lemma left_mem_interval : a ∈ a..b :=
by { rw interval, split_ifs with h, { rwa left_mem_Icc }, simp [le_of_not_le h] }

@[simp] lemma right_mem_interval : b ∈ a..b :=
by { rw interval_swap, exact left_mem_interval }

lemma mem_interval_of_mem_Icc (h : x ∈ Icc a b) : x ∈ a..b :=
by { rwa interval_of_le, exact le_trans h.1 h.2 }

lemma mem_interval_of_mem_Icc' (h : x ∈ Icc b a) : x ∈ a..b :=
by { rw interval_swap, exact mem_interval_of_mem_Icc h }

lemma mem_interval_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ a..b :=
mem_interval_of_mem_Icc ⟨ha, hb⟩

lemma mem_interval_of_le' (hb : b ≤ x) (ha : x ≤ a) : x ∈ a..b :=
mem_interval_of_mem_Icc' ⟨hb, ha⟩

lemma interval_subset_interval (h₁ : a₁ ∈ a₂..b₂) (h₂ : b₁ ∈ a₂..b₂) : a₁..b₁ ⊆ a₂..b₂ :=
begin
  unfold interval,
  split_ifs with h h' h',
  { rw [interval_of_le] at *,
    exact Icc_subset_Icc h₁.1 h₂.2,
    assumption' },
  { rw [interval_of_not_le] at *,
    exact Icc_subset_Icc h₁.1 h₂.2,
    assumption' },
  { rw [interval_of_le] at *,
    exact Icc_subset_Icc h₂.1 h₁.2,
    assumption' },
  { rw [interval_of_not_le] at *,
    exact Icc_subset_Icc h₂.1 h₁.2,
    assumption' },
end

lemma interval_subset_interval_iff : a₁..b₁ ⊆ a₂..b₂ ↔ a₁ ∈ a₂..b₂ ∧ b₁ ∈ a₂..b₂ :=
iff.intro (λh, ⟨h left_mem_interval, h right_mem_interval⟩) (λ h, interval_subset_interval h.1 h.2)

lemma interval_subset_interval_right (h : x ∈ a..b) : x..b ⊆ a..b :=
interval_subset_interval h right_mem_interval

lemma interval_subset_interval_left (h : x ∈ a..b) : a..x ⊆ a..b :=
interval_subset_interval left_mem_interval h

lemma Icc_subset_interval_self : Icc a b ⊆ a..b := assume x, mem_interval_of_mem_Icc

lemma bdd_below_bdd_above_iff_subset_interval (s : set α) :
  bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ a..b :=
begin
  rw [bdd_below_bdd_above_iff_subset_Icc],
  split,
  { rintros ⟨a, b, h⟩, exact ⟨a, b, λ x hx, mem_interval_of_mem_Icc (h hx)⟩ },
  { rintros ⟨a, b, h⟩,
    cases le_total a b with ab ba,
    { refine ⟨a, b, _⟩, rwa interval_of_le ab at h },
    { refine ⟨b, a, _⟩, rwa interval_of_le' ba at h } }
end

end decidable_linear_order

open_locale interval

section ordered_comm_group

variables {α : Type u} [decidable_linear_ordered_comm_group α] {a b x y : α}

/-- If `x..y` is a subinterval of `a..b`, then the distance between `x` and `y`
is less than or equal to that of `a` and `b` -/
lemma abs_sub_le_of_subinterval (h : x..y ⊆ a..b) : abs (y - x) ≤ abs (b - a) :=
begin
  rw abs_sub_le_iff,
  cases le_total a b with ab ba,
  { simp only [interval_of_le ab] at h,
    rw abs_of_nonneg (sub_nonneg_of_le ab),
    exact ⟨sub_le_sub (h right_mem_interval).2 (h left_mem_interval).1,
           sub_le_sub (h left_mem_interval).2 (h right_mem_interval).1⟩ },
  { simp only [interval_of_le' ba] at h,
    rw [abs_of_nonpos (sub_nonpos_of_le ba), neg_sub],
    exact ⟨sub_le_sub (h right_mem_interval).2 (h left_mem_interval).1,
           sub_le_sub (h left_mem_interval).2 (h right_mem_interval).1⟩ }
end

/-- If `x ∈ a..b`, then the distance between `a` and `x` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_left_of_mem_interval (h : x ∈ a..b) : abs (x - a) ≤ abs (b - a) :=
abs_sub_le_of_subinterval (interval_subset_interval_left h)

/-- If `x ∈ a..b`, then the distance between `x` and `b` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_right_of_mem_interval (h : x ∈ a..b) : abs (b - x) ≤ abs (b - a) :=
abs_sub_le_of_subinterval (interval_subset_interval_right h)

end ordered_comm_group

end set
