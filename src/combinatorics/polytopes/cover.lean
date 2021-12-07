/-
Copyright (c) 2021 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import .mathlib

/-!
# Covering relation
-/

open nat

variables {α β : Type*}

/-- One element covers another when there's no other element strictly in between. -/
def covers [preorder α] (y x : α) : Prop := x < y ∧ ∀ z, ¬ z ∈ set.Ioo x y

notation x ` ⋗ `:50 y:50 := covers x y
notation x ` ⋖ `:50 y:50 := covers y x

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
lemma exists_lt_lt_of_not_cover [preorder α] {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; exact hnxy ⟨hxy, λ z ⟨hl, hr⟩, hne z hl hr⟩

/-- If an element covers another, they define an empty open interval. -/
lemma set.Ioo_is_empty_of_covers [preorder α] {x y : α} : x ⋖ y → set.Ioo x y = ∅ :=
λ ⟨_, hr⟩, set.eq_empty_iff_forall_not_mem.2 hr

/-- A natural covers another iff it's a successor. -/
lemma nat.cover_iff_succ {m n : ℕ} : m ⋖ n ↔ n = m + 1 :=
begin
  split,
  { rintro ⟨hmnl, hmnr⟩,
    cases le_or_gt n (m + 1) with hnm hnm,
    exact antisymm hnm (nat.succ_le_of_lt hmnl),
    exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim },
  intro hnm,
  split,
  { rw hnm,
    exact lt_add_one m },
  rintro r ⟨hrl, hrr⟩,
  rw hnm at hrr,
  exact nat.lt_irrefl _ (lt_of_le_of_lt (nat.succ_le_of_lt hrl) hrr),
end

/-- Two `fin`s cover each other iff their values do. -/
lemma fin.cover_iff_cover {n : ℕ} (a b : fin n) : a ⋖ b ↔ a.val ⋖ b.val :=
  ⟨ λ ⟨hl, hr⟩, ⟨hl, λ c hc, (hr ⟨c, lt_trans hc.right b.prop⟩) hc⟩,
  λ ⟨hl, hr⟩, ⟨hl, λ c hc, hr c hc⟩ ⟩

/-- Covering is irreflexive. -/
instance covers.is_irrefl [preorder α] : is_irrefl α (⋖) :=
⟨ λ _ ha, ne_of_lt ha.left rfl ⟩

lemma dual_cover_iff_cover [preorder α] (a b : α) :
  a ⋖ b ↔ @covers (order_dual α) _ a b :=
by split; repeat { exact λ ⟨habl, habr⟩, ⟨habl, λ c ⟨hcl, hcr⟩, habr c ⟨hcr, hcl⟩⟩ }

lemma is_simple_order.bot_covers_top [partial_order α] [bounded_order α] [is_simple_order α] :
  (⊥ : α) ⋖ ⊤ :=
⟨bot_lt_top, λ a ha, (is_simple_order.eq_bot_or_eq_top a).elim ha.1.ne' ha.2.ne⟩
