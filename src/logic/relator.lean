/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/

namespace relator
universe variables u₁ u₂ v₁ v₂

reserve infixr ` ⇒ `:40

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
variables {α : Type u₁} {β : out_param $ Type u₂} (R : out_param $ α → β → Prop)

@[class] def right_total := ∀b, ∃a, R a b
@[class] def left_total := ∀a, ∃b, R a b
@[class] def bi_total := left_total R ∧ right_total R

end

section
variables {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

@[class] def left_unique := ∀{a b c}, R a b → R c b → a = c
@[class] def right_unique := ∀{a b c}, R a b → R a c → b = c

lemma rel_forall_of_right_total [t : right_total R] :
  ((R ⇒ implies) ⇒ implies) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel H b, exists.elim (t b) (assume a Rab, Hrel Rab (H _))

lemma rel_exists_of_left_total [t : left_total R] :
  ((R ⇒ implies) ⇒ implies) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel ⟨a, pa⟩, let ⟨b, Rab⟩ := t a in ⟨b, Hrel Rab pa⟩

lemma rel_forall_of_total [t : bi_total R] : ((R ⇒ iff) ⇒ iff) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel,
  ⟨assume H b, exists.elim (t.right b) (assume a Rab, (Hrel Rab).mp (H _)),
    assume H a, exists.elim (t.left a) (assume b Rab, (Hrel Rab).mpr (H _))⟩

lemma rel_exists_of_total [t : bi_total R] : ((R ⇒ iff) ⇒ iff) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel,
  ⟨assume ⟨a, pa⟩, let ⟨b, Rab⟩ := t.left a in ⟨b, (Hrel Rab).1 pa⟩,
    assume ⟨b, qb⟩, let ⟨a, Rab⟩ := t.right b in ⟨a, (Hrel Rab).2 qb⟩⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ iff)) eq eq') : left_unique R
| a b c (ab : R a b) (cb : R c b) :=
have eq' b b,
  from iff.mp (he ab ab) rfl,
iff.mpr (he ab cb) this

end

lemma rel_imp : (iff ⇒ (iff  ⇒ iff)) implies implies :=
assume p q h r s l, imp_congr h l

lemma rel_not : (iff ⇒ iff) not not :=
assume p q h, not_congr h

@[priority 100] -- see Note [lower instance priority]
-- (this is an instance is always applies, since the relation is an out-param)
instance bi_total_eq {α : Type u₁} : relator.bi_total (@eq α) :=
⟨assume a, ⟨a, rfl⟩, assume a, ⟨a, rfl⟩⟩

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

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
