/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.basic

/-!
# Nonempty types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves a few extra facts about `nonempty`, which is defined in core Lean.

## Main declarations

* `nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` explicitly.
* `classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` as an
  instance.
-/

variables {α β : Type*} {γ : α → Type*}

attribute [simp] nonempty_of_inhabited

@[priority 20]
instance has_zero.nonempty [has_zero α] : nonempty α := ⟨0⟩
@[priority 20]
instance has_one.nonempty [has_one α] : nonempty α := ⟨1⟩

lemma exists_true_iff_nonempty {α : Sort*} : (∃a:α, true) ↔ nonempty α :=
iff.intro (λ⟨a, _⟩, ⟨a⟩) (λ⟨a⟩, ⟨a, trivial⟩)

@[simp] lemma nonempty_Prop {p : Prop} : nonempty p ↔ p :=
iff.intro (assume ⟨h⟩, h) (assume h, ⟨h⟩)

lemma not_nonempty_iff_imp_false {α : Sort*} : ¬ nonempty α ↔ α → false :=
⟨λ h a, h ⟨a⟩, λ h ⟨a⟩, h a⟩

@[simp] lemma nonempty_sigma : nonempty (Σa:α, γ a) ↔ (∃a:α, nonempty (γ a)) :=
iff.intro (assume ⟨⟨a, c⟩⟩, ⟨a, ⟨c⟩⟩) (assume ⟨a, ⟨c⟩⟩, ⟨⟨a, c⟩⟩)

@[simp] lemma nonempty_psigma {α} {β : α → Sort*} : nonempty (psigma β) ↔ (∃a:α, nonempty (β a)) :=
iff.intro (assume ⟨⟨a, c⟩⟩, ⟨a, ⟨c⟩⟩) (assume ⟨a, ⟨c⟩⟩, ⟨⟨a, c⟩⟩)

@[simp] lemma nonempty_subtype {α} {p : α → Prop} : nonempty (subtype p) ↔ (∃a:α, p a) :=
iff.intro (assume ⟨⟨a, h⟩⟩, ⟨a, h⟩) (assume ⟨a, h⟩, ⟨⟨a, h⟩⟩)

@[simp] lemma nonempty_prod : nonempty (α × β) ↔ (nonempty α ∧ nonempty β) :=
iff.intro (assume ⟨⟨a, b⟩⟩, ⟨⟨a⟩, ⟨b⟩⟩) (assume ⟨⟨a⟩, ⟨b⟩⟩, ⟨⟨a, b⟩⟩)

@[simp] lemma nonempty_pprod {α β} : nonempty (pprod α β) ↔ (nonempty α ∧ nonempty β) :=
iff.intro (assume ⟨⟨a, b⟩⟩, ⟨⟨a⟩, ⟨b⟩⟩) (assume ⟨⟨a⟩, ⟨b⟩⟩, ⟨⟨a, b⟩⟩)

@[simp] lemma nonempty_sum : nonempty (α ⊕ β) ↔ (nonempty α ∨ nonempty β) :=
iff.intro
  (assume ⟨h⟩, match h with sum.inl a := or.inl ⟨a⟩ | sum.inr b := or.inr ⟨b⟩ end)
  (assume h, match h with or.inl ⟨a⟩ := ⟨sum.inl a⟩ | or.inr ⟨b⟩ := ⟨sum.inr b⟩ end)

@[simp] lemma nonempty_psum {α β} : nonempty (psum α β) ↔ (nonempty α ∨ nonempty β) :=
iff.intro
  (assume ⟨h⟩, match h with psum.inl a := or.inl ⟨a⟩ | psum.inr b := or.inr ⟨b⟩ end)
  (assume h, match h with or.inl ⟨a⟩ := ⟨psum.inl a⟩ | or.inr ⟨b⟩ := ⟨psum.inr b⟩ end)

@[simp] lemma nonempty_empty : ¬ nonempty empty :=
assume ⟨h⟩, h.elim

@[simp] lemma nonempty_ulift : nonempty (ulift α) ↔ nonempty α :=
iff.intro (assume ⟨⟨a⟩⟩, ⟨a⟩) (assume ⟨a⟩, ⟨⟨a⟩⟩)

@[simp] lemma nonempty_plift {α} : nonempty (plift α) ↔ nonempty α :=
iff.intro (assume ⟨⟨a⟩⟩, ⟨a⟩) (assume ⟨a⟩, ⟨⟨a⟩⟩)

@[simp] lemma nonempty.forall {α} {p : nonempty α → Prop} : (∀h:nonempty α, p h) ↔ (∀a, p ⟨a⟩) :=
iff.intro (assume h a, h _) (assume h ⟨a⟩, h _)

@[simp] lemma nonempty.exists {α} {p : nonempty α → Prop} : (∃h:nonempty α, p h) ↔ (∃a, p ⟨a⟩) :=
iff.intro (assume ⟨⟨a⟩, h⟩, ⟨a, h⟩) (assume ⟨a, h⟩, ⟨⟨a⟩, h⟩)

/-- Using `classical.choice`, lifts a (`Prop`-valued) `nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def classical.inhabited_of_nonempty' {α} [h : nonempty α] : inhabited α :=
⟨classical.choice h⟩

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible] protected noncomputable def nonempty.some {α} (h : nonempty α) : α :=
classical.choice h

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible] protected noncomputable def classical.arbitrary (α) [h : nonempty α] : α :=
classical.choice h

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
lemma nonempty.map {α β} (f : α → β) : nonempty α → nonempty β
| ⟨h⟩ := ⟨f h⟩

protected lemma nonempty.map2 {α β γ : Sort*} (f : α → β → γ) : nonempty α → nonempty β → nonempty γ
| ⟨x⟩ ⟨y⟩ := ⟨f x y⟩

protected lemma nonempty.congr {α β} (f : α → β) (g : β → α) :
  nonempty α ↔ nonempty β :=
⟨nonempty.map f, nonempty.map g⟩

lemma nonempty.elim_to_inhabited {α : Sort*} [h : nonempty α] {p : Prop}
  (f : inhabited α → p) : p :=
h.elim $ f ∘ inhabited.mk

instance {α β} [h : nonempty α] [h2 : nonempty β] : nonempty (α × β) :=
h.elim $ λ g, h2.elim $ λ g2, ⟨⟨g, g2⟩⟩

instance {ι : Sort*} {α : ι → Sort*} [Π i, nonempty (α i)] : nonempty (Π i, α i) :=
⟨λ _, classical.arbitrary _⟩

lemma classical.nonempty_pi {ι} {α : ι → Sort*} : nonempty (Π i, α i) ↔ ∀ i, nonempty (α i) :=
⟨λ ⟨f⟩ a, ⟨f a⟩, @pi.nonempty _ _⟩

lemma subsingleton_of_not_nonempty {α : Sort*} (h : ¬ nonempty α) : subsingleton α :=
⟨λ x, false.elim $ not_nonempty_iff_imp_false.mp h x⟩

lemma function.surjective.nonempty {α β : Sort*} [h : nonempty β] {f : α → β}
  (hf : function.surjective f) :
  nonempty α :=
let ⟨y⟩ := h, ⟨x, hx⟩ := hf y in ⟨x⟩
