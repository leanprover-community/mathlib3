/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.complete_boolean_algebra

/-!
# Interaction of relation properties with order operations

This file proves how `reflexive`, `irreflexive` and `symmetric` interact with lattice and boolean
operations.
-/

section reflexive
variables {ι : Sort*} {α : Type*} {r r₁ r₂ : α → α → Prop} {f : ι → α → α → Prop}
  {s : set (α → α → Prop)}

lemma reflexive.mono (hr : r₁ ≤ r₂) : reflexive r₁ → reflexive r₂ := forall_imp $ λ _, hr _ _
lemma irreflexive.mono (hr : r₁ ≤ r₂) : irreflexive r₂ → irreflexive r₁ :=
forall_imp $ λ _, mt $ hr _ _

lemma reflexive_top : reflexive (⊤ : α → α → Prop) := λ _, trivial
lemma irreflexive_bot : irreflexive (⊥ : α → α → Prop) := λ _, id
lemma not_reflexive_bot [nonempty α] : ¬ reflexive (⊥ : α → α → Prop) := λ h, nonempty.elim ‹_› h
lemma not_irreflexive_top [nonempty α] : ¬ irreflexive (⊤ : α → α → Prop) :=
nonempty.elim ‹_› $ λ a h, h a trivial

lemma reflexive.inf (h₁ : reflexive r₁) (h₂ : reflexive r₂) : reflexive (r₁ ⊓ r₂) :=
λ a, ⟨h₁ _, h₂ _⟩
lemma irreflexive.sup (h₁ : irreflexive r₁) (h₂ : irreflexive r₂) : irreflexive (r₁ ⊔ r₂) :=
λ a h, h.elim (h₁ _) (h₂ _)

@[simp] lemma reflexive_compl : reflexive rᶜ ↔ irreflexive r := iff.rfl
@[simp] lemma irreflexive_compl : irreflexive rᶜ ↔ reflexive r := forall_congr $ λ _, not_not

alias reflexive_compl ↔ reflexive.of_compl irreflexive.compl
alias irreflexive_compl ↔ iireflexive.of_compl reflexive.compl

lemma reflexive.not_compl [nonempty α] (hr : reflexive r) : ¬ reflexive rᶜ :=
λ h, nonempty.elim ‹_› $ λ a, h a $ hr _

lemma irreflexive.not_compl [nonempty α] (hr : irreflexive r) : ¬ irreflexive rᶜ :=
λ h, nonempty.elim ‹_› $ λ a, h a $ hr _

lemma reflexive.sdiff (h₁ : reflexive r₁) (h₂ : irreflexive r₂) : reflexive (r₁ \ r₂) :=
h₁.inf h₂.compl
lemma irreflexive.himp (h₁ : reflexive r₁) (h₂ : irreflexive r₂) : irreflexive (r₁ ⇨ r₂) :=
λ a h, h₂ _ $ h $ h₁ _

lemma reflexive_infi (hf : ∀ i, reflexive (f i)) : reflexive (⨅ i, f i) :=
λ a, by { simp only [infi_apply, infi_Prop_eq], exact λ i, hf _ _ }

lemma irreflexive_supr (hf : ∀ i, irreflexive (f i)) : irreflexive (⨆ i, f i) :=
λ a, by { simp only [supr_apply, supr_Prop_eq], exact not_exists.2 (λ i, hf _ _) }

lemma reflexive_Inf (hs : ∀ r ∈ s, reflexive r) : reflexive (Inf s) :=
by { rw Inf_eq_infi, exact reflexive_infi (λ r, reflexive_infi $ hs _) }

lemma irreflexive_Sup (hs : ∀ r ∈ s, irreflexive r) : irreflexive (Sup s) :=
by { rw Sup_eq_supr, exact irreflexive_supr (λ r, irreflexive_supr $ hs _) }

end reflexive

section symmetric
variables {ι : Sort*} {α : Type*} {r r₁ r₂ : α → α → Prop}

lemma symmetric_bot : symmetric (⊥ : α → α → Prop) := λ _ _, id
lemma symmetric_top : symmetric (⊤ : α → α → Prop) := λ _ _, id

lemma symmetric.sup (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ ⊔ r₂) :=
λ a b, or.imp (@h₁ _ _) $ @h₂ _ _

lemma symmetric.inf (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ ⊓ r₂) :=
λ a b h, ⟨h₁ h.1, h₂ h.2⟩

lemma symmetric.compl (hr : symmetric r) : symmetric rᶜ := λ a b, mt $ @hr _ _

lemma symmetric.sdiff (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ \ r₂) :=
h₁.inf h₂.compl

lemma symmetric.himp (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ ⇨ r₂) :=
λ a b hab hba, h₂ $ hab $ h₁ hba

lemma symmetric.symm_diff (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ ∆ r₂) :=
(h₁.sdiff h₂).sup (h₂.sdiff h₁)

lemma symmetric.bihimp (h₁ : symmetric r₁) (h₂ : symmetric r₂) : symmetric (r₁ ⇔ r₂) :=
(h₂.himp h₁).inf (h₁.himp h₂)

lemma symmetric_supr {f : ι → α → α → Prop} (hf : ∀ i, symmetric (f i)) : symmetric (⨆ i, f i) :=
λ a b, by { simp only [supr_apply, supr_Prop_eq, forall_exists_index], exact λ i h, ⟨i, hf _ h⟩ }

lemma symmetric_infi {f : ι → α → α → Prop} (hf : ∀ i, symmetric (f i)) : symmetric (⨅ i, f i) :=
λ a b, by { simp only [infi_apply, infi_Prop_eq], exact λ h i, hf _ (h _) }

lemma symmetric_Sup {s : set (α → α → Prop)} (hs : ∀ r ∈ s, symmetric r) : symmetric (Sup s) :=
by { rw Sup_eq_supr, exact symmetric_supr (λ r, symmetric_supr $ hs _) }

lemma symmetric_Inf {s : set (α → α → Prop)} (hs : ∀ r ∈ s, symmetric r) : symmetric (Inf s) :=
by { rw Inf_eq_infi, exact symmetric_infi (λ r, symmetric_infi $ hs _) }

end symmetric
