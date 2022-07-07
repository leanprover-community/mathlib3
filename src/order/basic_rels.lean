/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios
-/

import order.rel_classes

/-!
# Basic relations

We define two basic relations from any other relation `r`: the antisymmetrization or
indistinguishable relation `r a b ∧ r b a`, and the incomparable relation `¬ r a b ∧ ¬ r b a`.
-/

open function

variables {α β : Type*} (r : α → α → Prop)

/-! ### Antisymmetrization relation -/

section antisymm

/-- The antisymmetrization relation. -/
def antisymm_rel (a b : α) : Prop := r a b ∧ r b a

lemma antisymm_rel_swap : antisymm_rel (swap r) = antisymm_rel r :=
funext $ λ _, funext $ λ _, propext and.comm

@[refl] lemma antisymm_rel_refl [is_refl α r] (a : α) : antisymm_rel r a a := ⟨refl _, refl _⟩

instance [is_refl α r] : is_refl α (antisymm_rel r) := ⟨antisymm_rel_refl r⟩

lemma eq.antisymm_rel [is_refl α r] {a b : α} (h : a = b) : antisymm_rel r a b := by rw h

variables {r}

@[symm] lemma antisymm_rel.symm {a b : α} : antisymm_rel r a b → antisymm_rel r b a := and.symm

instance : is_symm α (antisymm_rel r) := ⟨λ a b, antisymm_rel.symm⟩

lemma antisymm_rel.comm {a b : α} : antisymm_rel r a b ↔ antisymm_rel r b a := comm

@[trans] lemma antisymm_rel.trans [is_trans α r] {a b c : α} (hab : antisymm_rel r a b)
  (hbc : antisymm_rel r b c) : antisymm_rel r a c :=
⟨trans hab.1 hbc.1, trans hbc.2 hab.2⟩

instance [is_trans α r] : is_trans α (antisymm_rel r) := ⟨λ a b c, antisymm_rel.trans⟩

instance antisymm_rel.decidable_rel [decidable_rel r] : decidable_rel (antisymm_rel r) :=
λ _ _, and.decidable

@[simp] lemma antisymm_rel_iff_eq [is_refl α r] [is_antisymm α r] {a b : α} :
  antisymm_rel r a b ↔ a = b := antisymm_iff

alias antisymm_rel_iff_eq ↔ antisymm_rel.eq _

lemma le_iff_lt_or_antisymm_rel [preorder α] {a b : α} : a ≤ b ↔ a < b ∨ antisymm_rel (≤) a b :=
by { rw [lt_iff_le_not_le, antisymm_rel], tauto! }

end antisymm

/-! ### Incomparable relation -/

section incomp

/-- The incomparability relation. -/
def incomp_rel (a b : α) : Prop := ¬ r a b ∧ ¬ r b a

lemma incomp_rel_swap : incomp_rel (swap r) = incomp_rel r := antisymm_rel_swap _

@[refl] lemma incomp_rel_refl [is_irrefl α r] (a : α) : incomp_rel r a a := ⟨irrefl _, irrefl _⟩

instance [is_irrefl α r] : is_refl α (incomp_rel r) := ⟨incomp_rel_refl r⟩

variables {r}

@[symm] lemma incomp_rel.symm {a b : α} : incomp_rel r a b → incomp_rel r b a := and.symm

instance : is_symm α (incomp_rel r) := ⟨λ a b, incomp_rel.symm⟩

lemma incomp_rel.comm {a b : α} : incomp_rel r a b ↔ incomp_rel r b a := comm

instance incomp_rel.decidable_rel [decidable_rel r] : decidable_rel (incomp_rel r) :=
λ _ _, and.decidable

@[simp] lemma not_incomp_rel [is_total α r] (a b : α) : ¬ incomp_rel r a b :=
by { rw [incomp_rel, not_and_distrib, not_not, not_not], exact is_total.total a b }

end incomp

/-- Two elements in a preorder compare as either less than, or equivalent (up to antisymmetry), or
greater than, or are incomparable. In fact, exactly one of them holds: see `preordering.precmp`. -/
lemma lt_or_antisymm_rel_or_gt_or_incomp_rel [preorder α] (a b : α) :
  a < b ∨ antisymm_rel (≤) a b ∨ b < a ∨ incomp_rel (≤) a b :=
by { rw [antisymm_rel, incomp_rel, lt_iff_le_not_le, lt_iff_le_not_le], tauto! }
