/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

This is an extension of `init/relator.lean`
-/
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

namespace relator

def bi_unique (r : α → β → Prop) : Prop := left_unique r ∧ right_unique r

lemma left_unique_flip (h : left_unique r) : right_unique (flip r)
| a b c h₁ h₂ := h h₁ h₂

lemma rel_and : ((↔) ⇒ (↔) ⇒ (↔)) (∧) (∧) :=
assume a b h₁ c d h₂, and_congr h₁ h₂

lemma rel_or : ((↔) ⇒ (↔) ⇒ (↔)) (∨) (∨) :=
assume a b h₁ c d h₂, or_congr h₁ h₂

lemma rel_iff : ((↔) ⇒ (↔) ⇒ (↔)) (↔) (↔) :=
assume a b h₁ c d h₂, iff_congr h₁ h₂

lemma rel_eq {r : α → β → Prop} (hr : bi_unique r) : (r ⇒ r ⇒ (↔)) (=) (=) :=
assume a b h₁ c d h₂,
iff.intro
  begin intro h, subst h, exact hr.right h₁ h₂ end
  begin intro h, subst h, exact hr.left h₁ h₂ end

end relator
