/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/

import tactic.reserved_notation

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
variables {α : Type u₁} {β : out_param $ Type u₂} (R : out_param $ α → β → Prop)

class right_total : Prop := (right : ∀b, ∃a, R a b)
class left_total : Prop := (left : ∀a, ∃b, R a b)
class bi_total extends left_total R, right_total R : Prop

end

section
variables {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

class left_unique : Prop := (left : ∀{a b c}, R a b → R c b → a = c)
class right_unique : Prop := (right : ∀{a b c}, R a b → R a c → b = c)

lemma left_unique.unique {R : α → β → Prop} (h : left_unique R) {a b c} :
  R a b → R c b → a = c := left_unique.left β

lemma right_unique.unique {R : α → β → Prop} (h : right_unique R) {a b c} :
  R a b → R a c → b = c := right_unique.right α

lemma rel_forall_of_right_total [right_total R] :
  ((R ⇒ implies) ⇒ implies) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel H b, exists.elim (right_total.right b) (assume a Rab, Hrel Rab (H _))

lemma rel_exists_of_left_total [left_total R] :
  ((R ⇒ implies) ⇒ implies) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel ⟨a, pa⟩, let ⟨b, Rab⟩ := left_total.left a in ⟨b, Hrel Rab pa⟩

lemma rel_forall_of_total [bi_total R] : ((R ⇒ iff) ⇒ iff) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel,
  ⟨assume H b, exists.elim (right_total.right b) (assume a Rab, (Hrel Rab).mp (H _)),
    assume H a, exists.elim (left_total.left a) (assume b Rab, (Hrel Rab).mpr (H _))⟩

lemma rel_exists_of_total [bi_total R] : ((R ⇒ iff) ⇒ iff) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel,
  ⟨assume ⟨a, pa⟩, let ⟨b, Rab⟩ := left_total.left a in ⟨b, (Hrel Rab).1 pa⟩,
    assume ⟨b, qb⟩, let ⟨a, Rab⟩ := right_total.right b in ⟨a, (Hrel Rab).2 qb⟩⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ iff)) eq eq') : left_unique R :=
⟨λ a b c (ab : R a b) (cb : R c b),
have eq' b b,
  from iff.mp (he ab ab) rfl,
iff.mpr (he ab cb) this⟩

end

lemma rel_imp : (iff ⇒ (iff  ⇒ iff)) implies implies :=
assume p q h r s l, imp_congr h l

lemma rel_not : (iff ⇒ iff) not not :=
assume p q h, not_congr h

@[priority 100] -- see Note [lower instance priority]
-- (this is an instance is always applies, since the relation is an out-param)
instance bi_total_eq {α : Type u₁} : relator.bi_total (@eq α) :=
{ left := λ a, ⟨a, rfl⟩, right := λ a, ⟨a, rfl⟩ }

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

class bi_unique (r : α → β → Prop) extends left_unique r, right_unique r : Prop

lemma left_unique_flip : left_unique r → right_unique (flip r)
| ⟨h⟩ := ⟨λ a b c h₁ h₂, h h₁ h₂⟩

lemma rel_and : ((↔) ⇒ (↔) ⇒ (↔)) (∧) (∧) :=
assume a b h₁ c d h₂, and_congr h₁ h₂

lemma rel_or : ((↔) ⇒ (↔) ⇒ (↔)) (∨) (∨) :=
assume a b h₁ c d h₂, or_congr h₁ h₂

lemma rel_iff : ((↔) ⇒ (↔) ⇒ (↔)) (↔) (↔) :=
assume a b h₁ c d h₂, iff_congr h₁ h₂

lemma rel_eq {r : α → β → Prop} (hr : bi_unique r) : (r ⇒ r ⇒ (↔)) (=) (=) :=
assume a b h₁ c d h₂,
iff.intro
  begin intro h, subst h, exact right_unique.right α h₁ h₂ end
  begin intro h, subst h, exact left_unique.left β h₁ h₂ end

end relator
