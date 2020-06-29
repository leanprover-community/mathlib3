/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov
-/
import tactic.tauto
import algebra.order_functions
import algebra.ordered_field

/-!
# Intervals

In any preorder `α`, we define intervals (which on each side can be either infinite, open, or
closed) using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side. For instance,
`Ioc a b` denotes the inverval `(a, b]`.

This file contains these definitions, and basic facts on inclusion, intersection, difference of
intervals (where the precise statements may depend on the properties of the order, in particular
for some statements it should be `linear_order` or `densely_ordered`).

TODO: This is just the beginning; a lot of rules are missing
-/

universe u

namespace set

open set

section intervals
variables {α : Type u} [preorder α] {a a₁ a₂ b b₁ b₂ x : α}

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

@[simp] lemma left_mem_Ioo : a ∈ Ioo a b ↔ false := by simp [lt_irrefl]
@[simp] lemma left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp [le_refl]
@[simp] lemma left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp [le_refl]
@[simp] lemma left_mem_Ioc : a ∈ Ioc a b ↔ false := by simp [lt_irrefl]
lemma left_mem_Ici : a ∈ Ici a := by simp
@[simp] lemma right_mem_Ioo : b ∈ Ioo a b ↔ false := by simp [lt_irrefl]
@[simp] lemma right_mem_Ico : b ∈ Ico a b ↔ false := by simp [lt_irrefl]
@[simp] lemma right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp [le_refl]
@[simp] lemma right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp [le_refl]
lemma right_mem_Iic : a ∈ Iic a := by simp

@[simp] lemma dual_Ici : @Ici (order_dual α) _ a = @Iic α _ a := rfl
@[simp] lemma dual_Iic : @Iic (order_dual α) _ a = @Ici α _ a := rfl
@[simp] lemma dual_Ioi : @Ioi (order_dual α) _ a = @Iio α _ a := rfl
@[simp] lemma dual_Iio : @Iio (order_dual α) _ a = @Ioi α _ a := rfl
@[simp] lemma dual_Icc : @Icc (order_dual α) _ a b = @Icc α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ioc : @Ioc (order_dual α) _ a b = @Ico α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ico : @Ico (order_dual α) _ a b = @Ioc α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ioo : @Ioo (order_dual α) _ a b = @Ioo α _ b a :=
set.ext $ λ x, and_comm _ _

@[simp] lemma nonempty_Icc : (Icc a b).nonempty ↔ a ≤ b :=
⟨λ ⟨x, hx⟩, le_trans hx.1 hx.2, λ h, ⟨a, left_mem_Icc.2 h⟩⟩

@[simp] lemma nonempty_Ico : (Ico a b).nonempty ↔ a < b :=
⟨λ ⟨x, hx⟩, lt_of_le_of_lt hx.1 hx.2, λ h, ⟨a, left_mem_Ico.2 h⟩⟩

@[simp] lemma nonempty_Ioc : (Ioc a b).nonempty ↔ a < b :=
⟨λ ⟨x, hx⟩, lt_of_lt_of_le hx.1 hx.2, λ h, ⟨b, right_mem_Ioc.2 h⟩⟩

@[simp] lemma nonempty_Ici : (Ici a).nonempty := ⟨a, left_mem_Ici⟩

@[simp] lemma nonempty_Iic : (Iic a).nonempty := ⟨a, right_mem_Iic⟩

@[simp] lemma nonempty_Ioo [densely_ordered α] : (Ioo a b).nonempty ↔ a < b :=
⟨λ ⟨x, ha, hb⟩, lt_trans ha hb, dense⟩

@[simp] lemma nonempty_Ioi [no_top_order α] : (Ioi a).nonempty := no_top a

@[simp] lemma nonempty_Iio [no_bot_order α] : (Iio a).nonempty := no_bot a

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

lemma Ici_subset_Ici : Ici a ⊆ Ici b ↔ b ≤ a :=
⟨λ h, h $ left_mem_Ici, λ h x hx, le_trans h hx⟩

lemma Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b :=
@Ici_subset_Ici (order_dual α) _ _ _

lemma Ici_subset_Ioi : Ici a ⊆ Ioi b ↔ b < a :=
⟨λ h, h left_mem_Ici, λ h x hx, lt_of_lt_of_le h hx⟩

lemma Iic_subset_Iio : Iic a ⊆ Iio b ↔ a < b :=
⟨λ h, h right_mem_Iic, λ h x hx, lt_of_le_of_lt hx h⟩

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

lemma Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b := λ x, and.imp_right le_of_lt

lemma Ico_subset_Icc_self : Ico a b ⊆ Icc a b := λ x, and.imp_right le_of_lt

lemma Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := λ x, and.imp_left le_of_lt

lemma Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

lemma Ico_subset_Iio_self : Ico a b ⊆ Iio b := λ x, and.right

lemma Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := λ x, and.right

lemma Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := λ x, and.left

lemma Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := λ x, and.left

lemma Ioi_subset_Ici_self : Ioi a ⊆ Ici a := λx hx, le_of_lt hx

lemma Iio_subset_Iic_self : Iio a ⊆ Iic a := λx hx, le_of_lt hx

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

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
lemma Ioi_subset_Ioi (h : a ≤ b) : Ioi b ⊆ Ioi a :=
λx hx, lt_of_le_of_lt h hx

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
lemma Ioi_subset_Ici (h : a ≤ b) : Ioi b ⊆ Ici a :=
subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
lemma Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b :=
λx hx, lt_of_lt_of_le hx h

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
lemma Iio_subset_Iic (h : a ≤ b) : Iio a ⊆ Iic b :=
subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self

lemma Ici_inter_Iic : Ici a ∩ Iic b = Icc a b := rfl
lemma Ici_inter_Iio : Ici a ∩ Iio b = Ico a b := rfl
lemma Ioi_inter_Iic : Ioi a ∩ Iic b = Ioc a b := rfl
lemma Ioi_inter_Iio : Ioi a ∩ Iio b = Ioo a b := rfl

end intervals

section partial_order
variables {α : Type u} [partial_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
set.ext $ by simp [Icc, le_antisymm_iff, and_comm]

lemma Icc_diff_left : Icc a b \ {a} = Ioc a b :=
ext $ λ x, by simp [lt_iff_le_and_ne, eq_comm, and.right_comm]

lemma Icc_diff_right : Icc a b \ {b} = Ico a b :=
ext $ λ x, by simp [lt_iff_le_and_ne, and_assoc]

lemma Ico_diff_left : Ico a b \ {a} = Ioo a b :=
ext $ λ x, by simp [and.right_comm, ← lt_iff_le_and_ne, eq_comm]

lemma Ioc_diff_right : Ioc a b \ {b} = Ioo a b :=
ext $ λ x, by simp [and_assoc, ← lt_iff_le_and_ne]

lemma Icc_diff_both : Icc a b \ {a, b} = Ioo a b :=
by rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]

lemma Ici_diff_left : Ici a \ {a} = Ioi a :=
ext $ λ x, by simp [lt_iff_le_and_ne, eq_comm]

lemma Iic_diff_right : Iic a \ {a} = Iio a :=
ext $ λ x, by simp [lt_iff_le_and_ne]

lemma Ico_diff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} :=
by rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 $ left_mem_Ico.2 h)]

lemma Ioc_diff_Ioo_same (h : a < b) : Ioc a b \ Ioo a b = {b} :=
by rw [← Ioc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 $ right_mem_Ioc.2 h)]

lemma Icc_diff_Ico_same (h : a ≤ b) : Icc a b \ Ico a b = {b} :=
by rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 $ right_mem_Icc.2 h)]

lemma Icc_diff_Ioc_same (h : a ≤ b) : Icc a b \ Ioc a b = {a} :=
by rw [← Icc_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 $ left_mem_Icc.2 h)]

lemma Icc_diff_Ioo_same (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} :=
by { rw [← Icc_diff_both, diff_diff_cancel_left], simp [insert_subset, h] }

lemma Ici_diff_Ioi_same : Ici a \ Ioi a = {a} :=
by rw [← Ici_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 left_mem_Ici)]

lemma Iic_diff_Iio_same : Iic a \ Iio a = {a} :=
by rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 right_mem_Iic)]

lemma Ioi_union_left : Ioi a ∪ {a} = Ici a := ext $ λ x, by simp [eq_comm, le_iff_eq_or_lt]

lemma Iio_union_right : Iio a ∪ {a} = Iic a := ext $ λ x, le_iff_lt_or_eq.symm

lemma mem_Ici_Ioi_of_subset_of_subset {s : set α} (ho : Ioi a ⊆ s) (hc : s ⊆ Ici a) :
  s ∈ ({Ici a, Ioi a} : set (set α)) :=
classical.by_cases
  (λ h : a ∈ s, or.inl $ subset.antisymm hc $ by simp [← Ioi_union_left, insert_subset, *])
  (λ h, or.inr $ subset.antisymm (λ x hx, lt_of_le_of_ne (hc hx) (λ heq, h $ heq.symm ▸ hx)) ho)

lemma mem_Iic_Iio_of_subset_of_subset {s : set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) :
  s ∈ ({Iic a, Iio a} : set (set α)) :=
@mem_Ici_Ioi_of_subset_of_subset (order_dual α) _ a s ho hc

lemma mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : set α} (ho : Ioo a b ⊆ s) (hc : s ⊆ Icc a b) :
  s ∈ ({Icc a b, Ico a b, Ioc a b, Ioo a b} : set (set α)) :=
begin
  classical,
  by_cases ha : a ∈ s; by_cases hb : b ∈ s,
  { refine or.inl (subset.antisymm hc _),
    rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha,
      ← Icc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho },
  { refine (or.inr $ or.inl $ subset.antisymm _ _),
    { rw [← Icc_diff_right],
      exact subset_diff_singleton hc hb },
    { rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha] at ho } },
  { refine (or.inr $ or.inr $ or.inl $ subset.antisymm _ _),
    { rw [← Icc_diff_left],
      exact subset_diff_singleton hc ha },
    { rwa [← Ioc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho } },
  { refine (or.inr $ or.inr $ or.inr $ subset.antisymm _ ho),
    rw [← Ico_diff_left, ← Icc_diff_right],
    apply_rules [subset_diff_singleton] }
end

end partial_order

section linear_order
variables {α : Type u} [linear_order α] {a a₁ a₂ b b₁ b₂ : α}

lemma compl_Iic : (Iic a)ᶜ = Ioi a := ext $ λ _, not_le
lemma compl_Ici : (Ici a)ᶜ = Iio a := ext $ λ _, not_le
lemma compl_Iio : (Iio a)ᶜ = Ici a := ext $ λ _, not_lt
lemma compl_Ioi : (Ioi a)ᶜ = Iic a := ext $ λ _, not_lt

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

open_locale classical

@[simp] lemma Ioi_subset_Ioi_iff : Ioi b ⊆ Ioi a ↔ a ≤ b :=
begin
  refine ⟨λh, _, λh, Ioi_subset_Ioi h⟩,
  by_contradiction ba,
  exact lt_irrefl _ (h (not_le.mp ba))
end

@[simp] lemma Ioi_subset_Ici_iff [densely_ordered α] : Ioi b ⊆ Ici a ↔ a ≤ b :=
begin
  refine ⟨λh, _, λh, Ioi_subset_Ici h⟩,
  by_contradiction ba,
  obtain ⟨c, bc, ca⟩ : ∃c, b < c ∧ c < a := dense (not_le.mp ba),
  exact lt_irrefl _ (lt_of_lt_of_le ca (h bc))
end

@[simp] lemma Iio_subset_Iio_iff : Iio a ⊆ Iio b ↔ a ≤ b :=
begin
  refine ⟨λh, _, λh, Iio_subset_Iio h⟩,
  by_contradiction ab,
  exact lt_irrefl _ (h (not_le.mp ab))
end

@[simp] lemma Iio_subset_Iic_iff [densely_ordered α] : Iio a ⊆ Iic b ↔ a ≤ b :=
begin
  refine ⟨λh, _, λh, Iio_subset_Iic h⟩,
  by_contradiction ba,
  obtain ⟨c, bc, ca⟩ : ∃c, b < c ∧ c < a := dense (not_le.mp ba),
  exact lt_irrefl _ (lt_of_lt_of_le bc (h ca))
end

/-! ### Unions of adjacent intervals -/

/-! #### Two infinite intervals -/

@[simp] lemma Iic_union_Ici : Iic a ∪ Ici a = univ := eq_univ_of_forall (λ x, le_total x a)

@[simp] lemma Iio_union_Ici : Iio a ∪ Ici a = univ := eq_univ_of_forall (λ x, lt_or_le x a)

@[simp] lemma Iic_union_Ioi : Iic a ∪ Ioi a = univ := eq_univ_of_forall (λ x, le_or_lt x a)

/-! #### A finite and an infinite interval -/

@[simp] lemma Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b ∪ Ici b = Ioi a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (lt_of_lt_of_le h),
  λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

@[simp] lemma Icc_union_Ici_eq_Ioi (h : a ≤ b) : Icc a b ∪ Ici b = Ici a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (le_trans h),
  λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

@[simp] lemma Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b ∪ Ici b = Ioi a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (lt_of_lt_of_le h),
  λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

@[simp] lemma Ico_union_Ici_eq_Ioi (h : a ≤ b) : Ico a b ∪ Ici b = Ici a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (le_trans h),
  λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

@[simp] lemma Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : Ioc a b ∪ Ioi b = Ioi a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (lt_of_le_of_lt h),
  λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

@[simp] lemma Icc_union_Ioi_eq_Ioi (h : a ≤ b) : Icc a b ∪ Ioi b = Ici a :=
ext $ λ x, ⟨λ hx, hx.elim and.left (λ hx, le_trans h (le_of_lt hx)),
  λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)⟩

/-! #### An infinite and a finite interval -/

@[simp] lemma Iic_union_Icc_eq_Iic (h : a ≤ b) : Iic a ∪ Icc a b = Iic b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, le_trans hx h) and.right,
  λ hx, (le_total x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

@[simp] lemma Iic_union_Ico_eq_Iio (h : a < b) : Iic a ∪ Ico a b = Iio b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, lt_of_le_of_lt hx h) and.right,
  λ hx, (le_total x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

@[simp] lemma Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, le_trans (le_of_lt hx) h) and.right,
  λ hx, (lt_or_le x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

@[simp] lemma Iio_union_Ico_eq_Iio (h : a ≤ b) : Iio a ∪ Ico a b = Iio b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, lt_of_lt_of_le hx h) and.right,
  λ hx, (lt_or_le x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

@[simp] lemma Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, le_trans hx h) and.right,
  λ hx, (le_or_lt x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

@[simp] lemma Iic_union_Ioo_eq_Iio (h : a < b) : Iic a ∪ Ioo a b = Iio b :=
ext $ λ x, ⟨λ hx, hx.elim (λ hx, lt_of_le_of_lt hx h) and.right,
  λ hx, (le_or_lt x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)⟩

/-! #### Two finite intervals with a common point -/

@[simp] lemma Ioc_union_Ico_eq_Ioo {c} (h₁ : a < b) (h₂ : b < c) : Ioc a b ∪ Ico b c = Ioo a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_le_of_lt hx.2 h₂⟩) (λ hx, ⟨lt_of_lt_of_le h₁ hx.1, hx.2⟩),
   λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Icc_union_Ico_eq_Ico {c} (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ico b c = Ico a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_le_of_lt hx.2 h₂⟩) (λ hx, ⟨le_trans h₁ hx.1, hx.2⟩),
   λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Icc_union_Icc_eq_Icc {c} (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Icc b c = Icc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans hx.2 h₂⟩) (λ hx, ⟨le_trans h₁ hx.1, hx.2⟩),
   λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Ioc_union_Icc_eq_Ioc {c} (h₁ : a < b) (h₂ : b ≤ c) : Ioc a b ∪ Icc b c = Ioc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans hx.2 h₂⟩) (λ hx, ⟨lt_of_lt_of_le h₁ hx.1, hx.2⟩),
   λ hx, (le_total x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

/-! #### Two finite intervals, `I?o` and `Ic?` -/

@[simp] lemma Ioo_union_Ico_eq_Ioo {c} (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Ico b c = Ioo a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_lt_of_le hx.2 h₂⟩) (λ hx, ⟨lt_of_lt_of_le h₁ hx.1, hx.2⟩),
   λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Ico_union_Ico_eq_Ico {c} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Ico b c = Ico a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_lt_of_le hx.2 h₂⟩) (λ hx, ⟨le_trans h₁ hx.1, hx.2⟩),
   λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Ico_union_Icc_eq_Icc {c} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Icc b c = Icc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans (le_of_lt hx.2) h₂⟩) (λ hx, ⟨le_trans h₁ hx.1, hx.2⟩),
   λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Ioo_union_Icc_eq_Ioc {c} (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans (le_of_lt hx.2) h₂⟩) (λ hx, ⟨lt_of_lt_of_le h₁ hx.1, hx.2⟩),
   λ hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

/-! #### Two finite intervals, `I?c` and `Io?` -/

@[simp] lemma Ioc_union_Ioo_eq_Ioo {c} (h₁ : a ≤ b) (h₂ : b < c) : Ioc a b ∪ Ioo b c = Ioo a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_le_of_lt hx.2 h₂⟩) (λ hx, ⟨lt_of_le_of_lt h₁ hx.1, hx.2⟩),
   λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Icc_union_Ioo_eq_Ico {c} (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ioo b c = Ico a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, lt_of_le_of_lt hx.2 h₂⟩) (λ hx, ⟨le_trans h₁ (le_of_lt hx.1), hx.2⟩),
   λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Icc_union_Ioc_eq_Icc {c} (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Ioc b c = Icc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans hx.2 h₂⟩) (λ hx, ⟨le_trans h₁ (le_of_lt hx.1), hx.2⟩),
   λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

@[simp] lemma Ioc_union_Ioc_eq_Ioc {c} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c :=
ext $ λ x,
  ⟨λ hx, hx.elim (λ hx, ⟨hx.1, le_trans hx.2 h₂⟩) (λ hx, ⟨lt_of_le_of_lt h₁ hx.1, hx.2⟩),
   λ hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)⟩

end linear_order

section lattice


section inf

variables {α : Type u} [semilattice_inf α]

@[simp] lemma Iic_inter_Iic {a b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) :=
by { ext x, simp [Iic] }

@[simp] lemma Iio_inter_Iio [is_total α (≤)] {a b : α} : Iio a ∩ Iio b = Iio (a ⊓ b) :=
by { ext x, simp [Iio] }

end inf

section sup

variables {α : Type u} [semilattice_sup α]

@[simp] lemma Ici_inter_Ici {a b : α} : Ici a ∩ Ici b = Ici (a ⊔ b) :=
by { ext x, simp [Ici] }

@[simp] lemma Ioi_inter_Ioi [is_total α (≤)] {a b : α} : Ioi a ∩ Ioi b = Ioi (a ⊔ b) :=
by { ext x, simp [Ioi] }

end sup

section both

variables {α : Type u} [lattice α] [ht : is_total α (≤)] {a b c a₁ a₂ b₁ b₂ : α}

lemma Icc_inter_Icc : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_refl

@[simp] lemma Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) :
  Icc a b ∩ Icc b c = {b} :=
by rw [Icc_inter_Icc, sup_of_le_right hab, inf_of_le_left hbc, Icc_self]

include ht

lemma Ico_inter_Ico : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ici_inter_Iio.symm, Ici_inter_Ici.symm, Iio_inter_Iio.symm]; ac_refl

lemma Ioc_inter_Ioc : Ioc a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ioi_inter_Iic.symm, Ioi_inter_Ioi.symm, Iic_inter_Iic.symm]; ac_refl

lemma Ioo_inter_Ioo : Ioo a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ioi_inter_Iio.symm, Ioi_inter_Ioi.symm, Iio_inter_Iio.symm]; ac_refl

end both

end lattice

section decidable_linear_order
variables {α : Type u} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ : α}

@[simp] lemma Ico_diff_Iio {a b c : α} : Ico a b \ Iio c = Ico (max a c) b :=
set.ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio {a b c : α} : Ico a b ∩ Iio c = Ico a (min b c) :=
set.ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

end decidable_linear_order

section decidable_linear_ordered_add_comm_group

variables {α : Type u} [decidable_linear_ordered_add_comm_group α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
lemma nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
  nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp* },
  { use max x (x + dy), simp [*, le_refl] }
end

end decidable_linear_ordered_add_comm_group

end set
