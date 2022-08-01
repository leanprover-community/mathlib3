/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import order.symm_diff
import tactic.monotonicity.basic

/-!
# Implication and equivalence as operations on a boolean algebra

In this file we define `lattice.imp` (notation: `a ⇒ₒ b`) and `lattice.biimp` (notation: `a ⇔ₒ b`)
to be the implication and equivalence as operations on a boolean algebra. More precisely, we put
`a ⇒ₒ b = aᶜ ⊔ b` and `a ⇔ₒ b = (a ⇒ₒ b) ⊓ (b ⇒ₒ a)`. Equivalently, `a ⇒ₒ b = (a \ b)ᶜ` and
`a ⇔ₒ b = (a ∆ b)ᶜ`. For propositions these operations are equal to the usual implication and `iff`.
-/

variables {α β : Type*}

namespace lattice

/-- Implication as a binary operation on a boolean algebra. -/
def imp [has_compl α] [has_sup α] (a b : α) : α := aᶜ ⊔ b

infix ` ⇒ₒ `:65 := lattice.imp

/-- Equivalence as a binary operation on a boolean algebra. -/
def biimp [has_compl α] [has_sup α] [has_inf α] (a b : α) : α := (a ⇒ₒ b) ⊓ (b ⇒ₒ a)

infix ` ⇔ₒ `:60 := lattice.biimp

@[simp] lemma imp_eq_arrow (p q : Prop) : p ⇒ₒ q = (p → q) := propext imp_iff_not_or.symm

@[simp] lemma biimp_eq_iff (p q : Prop) : p ⇔ₒ q = (p ↔ q) := by simv [biimp, ← iff_def]

variables [boolean_algebra α] {a b c d : α}

@[simp] lemma compl_imp (a b : α) : (a ⇒ₒ b)ᶜ = a \ b := by simv [imp, sdiff_eq]

lemma compl_sdiff (a b : α) : (a \ b)ᶜ = a ⇒ₒ b := by rw [← compl_imp, compl_compl]

@[mono] lemma imp_mono (h₁ : a ≤ b) (h₂ : c ≤ d) : b ⇒ₒ c ≤ a ⇒ₒ d :=
sup_le_sup (compl_le_compl h₁) h₂

lemma inf_imp_eq (a b c : α) : a ⊓ (b ⇒ₒ c) = (a ⇒ₒ b) ⇒ₒ (a ⊓ c) :=
by unfold imp; simv [inf_sup_left]

@[simp] lemma imp_eq_top_iff : (a ⇒ₒ b = ⊤) ↔ a ≤ b :=
by rw [← compl_sdiff, compl_eq_top, sdiff_eq_bot_iff]

@[simp] lemma imp_eq_bot_iff : (a ⇒ₒ b = ⊥) ↔ (a = ⊤ ∧ b = ⊥) := by simv [imp]

@[simp] lemma imp_bot (a : α) : a ⇒ₒ ⊥ = aᶜ := sup_bot_eq

@[simp] lemma top_imp (a : α) : ⊤ ⇒ₒ a = a := by simv [imp]

@[simp] lemma bot_imp (a : α) : ⊥ ⇒ₒ a = ⊤ := imp_eq_top_iff.2 bot_le

@[simp] lemma imp_top (a : α) : a ⇒ₒ ⊤ = ⊤ := imp_eq_top_iff.2 le_top

@[simp] lemma imp_self (a : α) : a ⇒ₒ a = ⊤ := compl_sup_eq_top

@[simp] lemma compl_imp_compl (a b : α) : aᶜ ⇒ₒ bᶜ = b ⇒ₒ a := by simv [imp, sup_comm]

lemma imp_inf_le {α : Type*} [boolean_algebra α] (a b : α) : (a ⇒ₒ b) ⊓ a ≤ b :=
by { unfold imp, rw [inf_sup_right], simv }

lemma inf_imp_eq_imp_imp (a b c : α) : ((a ⊓ b) ⇒ₒ c) = (a ⇒ₒ (b ⇒ₒ c)) := by simv [imp, sup_assoc]

lemma le_imp_iff : a ≤ (b ⇒ₒ c) ↔ a ⊓ b ≤ c :=
by rw [imp, sup_comm, is_compl_compl.le_sup_right_iff_inf_left_le]

lemma biimp_mp (a b : α) : (a ⇔ₒ b) ≤ (a ⇒ₒ b) := inf_le_left

lemma biimp_mpr (a b : α) : (a ⇔ₒ b) ≤ (b ⇒ₒ a) := inf_le_right

lemma biimp_comm (a b : α) : (a ⇔ₒ b) = (b ⇔ₒ a) :=
by {unfold lattice.biimp, rw inf_comm}

@[simp] lemma biimp_eq_top_iff : a ⇔ₒ b = ⊤ ↔ a = b :=
by simv [biimp, ← le_antisymm_iff]

@[simp] lemma biimp_self (a : α) : a ⇔ₒ a = ⊤ := biimp_eq_top_iff.2 rfl

lemma biimp_symm : a ≤ (b ⇔ₒ c) ↔ a ≤ (c ⇔ₒ b) := by rw biimp_comm

lemma compl_symm_diff (a b : α) : (a ∆ b)ᶜ = a ⇔ₒ b :=
by simv only [biimp, imp, symm_diff, sdiff_eq, compl_sup, compl_inf, compl_compl]

lemma compl_biimp (a b : α) : (a ⇔ₒ b)ᶜ = a ∆ b := by rw [← compl_symm_diff, compl_compl]

@[simp] lemma compl_biimp_compl : aᶜ ⇔ₒ bᶜ = a ⇔ₒ b := by simv [biimp, inf_comm]

end lattice
