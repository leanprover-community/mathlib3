/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.bounded_lattice

/-!
# Successor and predecessor

-/

/-- Order equipped with a sensible successor function. -/
@[ext] class succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(le_succ : ∀ a, a ≤ succ a)
(maximal_of_succ_le : ∀ ⦃a⦄, succ a ≤ a → ∀ ⦃b⦄, ¬a < b)
(succ_le_of_lt : ∀ {a b}, a < b → succ a ≤ b)
(le_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b)

open succ_order

variables {α : Type*}

/-- A constructor taking -/
def succ_order_of_lt_succ_iff_le_of_lt_iff_succ_le [preorder α] {succ : α → α}
  (hlt_iff_succ_le : ∀ {a b}, a < b ↔ succ a ≤ b)
  (hlt_succ_iff_le : ∀ {a b}, a < succ b ↔ a ≤ b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hlt_succ_iff_le.2 le_rfl).le,
  maximal_of_succ_le := λ a ha, (lt_irrefl a (hlt_iff_succ_le.2 ha)).elim,
  succ_le_of_lt := λ a b, hlt_iff_succ_le.1,
  le_of_lt_succ := λ a b, hlt_succ_iff_le.1 }

section preorder
variables [preorder α] [succ_order α]

@[simp] lemma succ_le_succ_of_le {a b : α} (h : a ≤ b) :
  succ a ≤ succ b :=
begin
  by_cases ha : ∀ ⦃c⦄, ¬a < c,
  { have hba : succ b ≤ a,
    { by_contra H,
      exact ha ((h.trans (le_succ b)).lt_of_not_le H) },
    by_contra H,
    exact ha ((h.trans (le_succ b)).trans_lt ((hba.trans (le_succ a)).lt_of_not_le H)) },
  push_neg at ha,
  obtain ⟨c, hc⟩ := ha,
  exact succ_le_of_lt ((h.trans (le_succ b)).lt_of_not_le $ λ hba,
    maximal_of_succ_le (hba.trans h) (((le_succ b).trans hba).trans_lt hc)),
end

end preorder

section partial_order
variables [partial_order α]

lemma le_le_succ_iff [succ_order α] {a b : α} : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a :=
begin
  split,
  { rintro h,
    rw or_iff_not_imp_left,
    exact λ hba, h.2.antisymm (succ_le_of_lt $ h.1.lt_of_ne $ ne.symm hba) },
  rintro (rfl | rfl),
  { exact ⟨le_rfl, le_succ b⟩ },
  { exact ⟨le_succ a, le_rfl⟩ }
end

end partial_order

section no_top_order
variables [preorder α] [no_top_order α] [succ_order α]

lemma lt_succ (a : α) :
  a < succ a :=
(le_succ a).lt_of_not_le (λ h, not_exists.mpr (maximal_of_succ_le h) (no_top a))

lemma lt_succ_iff_le {a b : α} :
  a < succ b ↔ a ≤ b :=
⟨le_of_lt_succ, λ h, h.trans_lt (lt_succ b)⟩

lemma lt_iff_succ_le {a b : α} :
  a < b ↔ succ a ≤ b :=
⟨succ_le_of_lt, (lt_succ a).trans_le⟩

@[simp] lemma succ_le_succ_iff {a b : α} :
  succ a ≤ succ b ↔ a ≤ b :=
⟨λ h, le_of_lt_succ ((lt_succ a).trans_le h), λ h, succ_le_of_lt (h.trans_lt (lt_succ b))⟩

@[simp] lemma succ_lt_succ_iff {a b : α} :
  succ a < succ b ↔ a < b :=
by simp_rw [lt_iff_le_not_le, succ_le_succ_iff]

end no_top_order

section order_top
variables [order_top α] [succ_order α]

@[simp] lemma succ_top :
  succ (⊤ : α) = ⊤ :=
le_top.antisymm (le_succ _)

@[simp] lemma succ_le_iff_eq_top {a : α} :
  succ a ≤ a ↔ a = ⊤ :=
⟨λ h, eq_top_of_maximal (maximal_of_succ_le h), λ h, by rw [h, succ_top]⟩

@[simp] lemma lt_succ_iff_ne_top {a : α} : a < succ a ↔ a ≠ ⊤ :=
begin
  simp only [lt_iff_le_not_le, true_and, le_succ a],
  exact not_iff_not.2 succ_le_iff_eq_top,
end

end order_top

section order_bot

lemma bot_lt_succ [order_bot α] [nontrivial α] [succ_order α] (a : α) :
  ⊥ < succ a :=
begin
  obtain ⟨b, hb⟩ := exists_ne (⊥ : α),
  refine bot_lt_iff_ne_bot.2 (λ h, _),
  have := eq_bot_iff.2 ((le_succ a).trans h.le),
  rw this at h,
  exact maximal_of_succ_le h.le (bot_lt_iff_ne_bot.2 hb),
end

end order_bot

/-- Class stating that `∀ a b, a < b ↔ a + 1 ≤ b` and `∀ a b, a < b + 1 ↔ a ≤ b`. -/
class succ_eq_add_one_order (α : Type*) [preorder α] [has_add α] [has_one α] extends
  succ_order α :=
(succ_eq_add_one : ∀ a, succ a = a + 1)

lemma lt_iff_add_one_le [preorder α] [no_top_order α] [has_add α] [has_one α]
  [succ_eq_add_one_order α] {a b : α} :
  a < b ↔ a + 1 ≤ b :=
by { rw ←succ_eq_add_one_order.succ_eq_add_one, exact lt_iff_succ_le }

lemma lt_add_one_iff_le [preorder α] [no_top_order α] [has_add α] [has_one α]
  [succ_eq_add_one_order α] {a b : α} :
  a < b + 1 ↔ a ≤ b :=
by { rw ←succ_eq_add_one_order.succ_eq_add_one, exact lt_succ_iff_le }
