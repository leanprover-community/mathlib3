/-
Copyright (c) 2021 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import .mathlib
import data.nat.succ_pred

/-!
# Covering relation
-/

open nat order_dual

variables {α β : Type*}

@[simp] lemma of_dual_covers_of_dual_iff {a b : order_dual α} [has_lt α] :
  of_dual a ⋖ of_dual b ↔ b ⋖ a :=
and_congr_right' $ forall_congr $ λ c, forall_swap

alias of_dual_covers_of_dual_iff ↔ _ covers.of_dual

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
lemma exists_lt_lt_of_not_covers [has_lt α] {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
(not_covers_iff hxy).1 hnxy

/-- A natural covers another iff it's a successor. -/
protected lemma nat.covers_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n := covers_iff_succ_eq

/-- Two `fin`s cover each other iff their values do. -/
@[simp] lemma fin.val_covers_iff {n : ℕ} (a b : fin n) : a.val ⋖ b.val ↔ a ⋖ b :=
and_congr_right' ⟨λ h c hc, h hc, λ h c ha hb, @h ⟨c, lt_trans hb b.prop⟩ ha hb⟩

@[simp] lemma of_dual_lt_of_dual_iff {a b : order_dual α} [has_lt α] :
  of_dual a < of_dual b ↔ b < a :=
iff.rfl

@[simp] lemma of_dual_le_of_dual_iff {a b : order_dual α} [has_le α] :
  of_dual a ≤ of_dual b ↔ b ≤ a :=
iff.rfl
