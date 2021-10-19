/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/

import logic.basic

namespace relator
universe variables u₁ u₂ v₁ v₂

/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/

section
variables {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variables (R : α → β → Prop) (S : γ → δ → Prop)

def lift_fun (f : α → γ) (g : β → δ) : Prop :=
∀⦃a b⦄, R a b → S (f a) (g b)

infixr ⇒ := lift_fun

end

section
variables {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

def right_total : Prop := ∀ b, ∃ a, R a b
def left_total : Prop := ∀ a, ∃ b, R a b
def bi_total : Prop := left_total R ∧ right_total R

def left_unique : Prop := ∀ ⦃a b c⦄, R a c → R b c → a = b
def right_unique : Prop := ∀ ⦃a b c⦄, R a b → R a c → b = c
def bi_unique : Prop := left_unique R ∧ right_unique R

variable {R}

lemma right_total.rel_forall (h : right_total R) :
  ((R ⇒ implies) ⇒ implies) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel H b, exists.elim (h b) (assume a Rab, Hrel Rab (H _))

lemma left_total.rel_exists (h : left_total R) :
  ((R ⇒ implies) ⇒ implies) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel ⟨a, pa⟩, (h a).imp $ λ b Rab, Hrel Rab pa

lemma bi_total.rel_forall (h : bi_total R) :
  ((R ⇒ iff) ⇒ iff) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel,
  ⟨assume H b, exists.elim (h.right b) (assume a Rab, (Hrel Rab).mp (H _)),
    assume H a, exists.elim (h.left a) (assume b Rab, (Hrel Rab).mpr (H _))⟩

lemma bi_total.rel_exists (h : bi_total R) : ((R ⇒ iff) ⇒ iff) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel,
  ⟨assume ⟨a, pa⟩, (h.left a).imp $ λ b Rab, (Hrel Rab).1 pa,
    assume ⟨b, qb⟩, (h.right b).imp $ λ a Rab, (Hrel Rab).2 qb⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ iff)) eq eq') : left_unique R :=
λ a b c (ac : R a c) (bc : R b c), (he ac bc).mpr ((he bc bc).mp rfl)

end

lemma rel_imp : (iff ⇒ (iff  ⇒ iff)) implies implies :=
assume p q h r s l, imp_congr h l

lemma rel_not : (iff ⇒ iff) not not :=
assume p q h, not_congr h

lemma bi_total_eq {α : Type u₁} : relator.bi_total (@eq α) :=
{ left := λ a, ⟨a, rfl⟩, right := λ a, ⟨a, rfl⟩ }

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

lemma left_unique.flip (h : left_unique r) : right_unique (flip r) :=
λ a b c h₁ h₂, h h₁ h₂

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
