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

/-- A natural covers another iff it's a successor. -/
protected lemma nat.covers_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n := covers_iff_succ_eq

/-- Two `fin`s cover each other iff their values do. -/
@[simp] lemma fin.val_covers_iff {n : ℕ} (a b : fin n) : a.val ⋖ b.val ↔ a ⋖ b :=
and_congr_right' ⟨λ h c hc, h hc, λ h c ha hb, @h ⟨c, lt_trans hb b.prop⟩ ha hb⟩
