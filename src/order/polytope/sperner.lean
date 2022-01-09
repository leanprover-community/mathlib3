/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.nat_antidiagonal
import data.finset.slice

/-!
# Sperner orders and Whitney numbers

-/

open finset

variables {α β : Type*}

/-! ### Slice orders -/

/-- A `slice_order` is an order whose "horizontal slices" (elements of a given grade) are finite.
This is the most general structure in which we can define Whitney numbers. -/
class slice_order (α : Type*) [preorder α] [order_bot α] [grade_order α] :=
(slice (n : ℕ) : finset α)
(mem_slice (n : ℕ) (a : α) : a ∈ slice n ↔ grade a = n)

section slice_order
section preorder
variables [preorder α]

section order_bot
variables (α) [order_bot α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

/-- The `n`-th slice of `α` is the finset of element of `α` of grade `n`. -/
def slice : finset α := slice_order.slice n

variables {α n}

@[simp] lemma mem_slice_iff : a ∈ slice α n ↔ grade a = n := slice_order.mem_slice _ _

lemma mem_slice_grade (a : α) : a ∈ slice α (grade a) := mem_slice_iff.2 rfl

@[reducible] -- See note [reducible non-instances]
def locally_finite_order.of_decidable_le_lt [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((<) : α → α → Prop)] (Icc Ico Ioc Ioo : α → α → finset α)
  (hIcc : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → x ∈ Icc a b)
  (hIco : ∀ ⦃a b x⦄, a ≤ x → x < b → x ∈ Ico a b)
  (hIoc : ∀ ⦃a b x⦄, a < x → x ≤ b → x ∈ Ioc a b)
  (hIoo : ∀ ⦃a b x⦄, a < x → x < b → x ∈ Ioo a b) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (Icc a b).filter (λ x, a ≤ x ∧ x ≤ b),
  finset_Ico := λ a b, (Ico a b).filter (λ x, a ≤ x ∧ x < b),
  finset_Ioc := λ a b, (Ioc a b).filter (λ x, a < x ∧ x ≤ b),
  finset_Ioo := λ a b, (Ioo a b).filter (λ x, a < x ∧ x < b),
  finset_mem_Icc := _,
  finset_mem_Ico := _,
  finset_mem_Ioc := _,
  finset_mem_Ioo := _ }

variables (α n)

lemma slice_nonempty [no_top_order α] : (slice α n).nonempty := sorry

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α] [slice_order α] {n : ℕ} {a : α}

lemma slice_nonempty_of_le (h : n ≤ grade (⊤ : α)) : (slice α n).nonempty := sorry

end bounded_order
end preorder

section partial_order
variables [partial_order α]

section order_bot
variables (α) [order_bot α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

lemma slice_zero : slice α 0 = {⊥} := sorry

@[reducible] -- See note [reducible non-instances]
def slice_order.to_locally_finite_order [decidable_eq α] [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((<) : α → α → Prop)] :
  locally_finite_order α :=
locally_finite_order.of_decidable_le_lt
  (λ a b, (Icc (grade a) (grade b)).sup $ slice α)
  (λ a b, (Ico (grade a) (grade b)).sup $ slice α)
  (λ a b, (Ioc (grade a) (grade b)).sup $ slice α)
  (λ a b, (Ioo (grade a) (grade b)).sup $ slice α)
  (λ a b x ha hb,
    mem_sup.2 ⟨grade x, mem_Icc.2 ⟨grade_mono ha, grade_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb,
    mem_sup.2 ⟨grade x, mem_Ico.2 ⟨grade_mono ha, grade_strict_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb,
    mem_sup.2 ⟨grade x, mem_Ioc.2 ⟨grade_strict_mono ha, grade_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb,
    mem_sup.2 ⟨grade x, mem_Ioo.2 ⟨grade_strict_mono ha, grade_strict_mono hb⟩, mem_slice_grade _⟩)

end order_bot

section bounded_order
variables (α) [bounded_order α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

lemma slice_grade_top : slice α (grade (⊤ : α)) = {⊤} := sorry

end bounded_order
end partial_order
end slice_order

/-! ### Whitney numbers -/

section whitney
section preorder
variables [preorder α]

section order_bot
variables (α) [order_bot α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

-- Is this worth a separate definition?
/-- The `n`-th Whitney number of `α`is the number of element of `α` of grade `n`. -/
def whitney_number : ℕ := (slice α n).card

lemma whitney_number_pos [no_top_order α] : 0 < whitney_number α n :=
card_pos.2 $ slice_nonempty _ _

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α] [slice_order α] {n : ℕ} {a : α}

lemma whitney_number_pos_of_le (h : n ≤ grade (⊤ : α)) : 0 < whitney_number α n :=
card_pos.2 $ slice_nonempty_of_le h

end bounded_order
end preorder

section partial_order
variables [partial_order α]

section order_bot
variables (α) [order_bot α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

lemma whitney_number_zero : whitney_number α 0 = 1 :=
by rw [whitney_number, slice_zero, card_singleton]

end order_bot

section bounded_order
variables (α) [bounded_order α] [grade_order α] [slice_order α] (n : ℕ) {a : α}

lemma whitney_number_grade_top : whitney_number α (grade (⊤ : α)) = 1 :=
by rw [whitney_number, slice_grade_top, card_singleton]

end bounded_order
end partial_order
end whitney

/-! ### Sperner orders -/

/-- An order has the Sperner property if all antichains are smaller than some slice of the order.
Sperner's theorem exactly claims that `finset α` has the Sperner property. -/
class is_sperner_order (α : Type*) [preorder α] [order_bot α] [grade_order α] [slice_order α] :
  Prop :=
(exists_le_whitney (s : finset α) : is_antichain (≤) (s : set α) → ∃ n, s.card ≤ whitney_number α n)

/-- An order has the strict Sperner property if all antichains are smaller than some slice of the
order and all maximal antichains are the size of some Whitney number. -/
class is_strict_sperner_order (α : Type*) [preorder α] [order_bot α] [grade_order α]
  [slice_order α] extends is_sperner_order α : Prop :=
(exists_eq_whitney (s : finset α) : is_antichain (≤) (s : set α) →
  (∀ t : finset α, is_antichain (≤) (t : set α) → s ⊆ t → s = t) → ∃ n, s.card = whitney_number α n)

/-! ### Instances -/

/-! ### Product of two slice orders -/

namespace prod
variables [partial_order α] [partial_order β] [order_bot α] [order_bot β] [grade_order α]
  [grade_order β] [slice_order α] [slice_order β] [decidable_eq (finset α × finset β)]

instance : slice_order (α × β) :=
{ slice := λ n, begin
    sorry
    -- have := (nat.antidiagonal n).image (prod.map (slice α) $ slice β),
  end,
  mem_slice := _ }

end prod
