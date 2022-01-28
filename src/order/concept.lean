/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.complete_lattice
import order.hom.basic

/-!
# Concept lattices

-/

variables {α β γ : Type*} (r : α → β → Prop)

def intent_closure (s : set α) : set β := {b | ∀ a ∈ s, r a b}

def extent_closure (t : set β) : set α := {a | ∀ b ∈ t, r a b}

@[simp] lemma intent_closure_union (s₁ s₂ : set α) :
  intent_closure r (s₁ ∪ s₂) = intent_closure r s₁ ∩ intent_closure r s₂ :=
set.ext $ λ _, ball_or_left_distrib

variables (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure concept :=
(fst : set α)
(snd : set β)
(closure_fst : intent_closure r fst = snd)
(closure_snd : extent_closure r snd = fst)

variables {α β}

instance : has_sup (concept α β r) :=
⟨λ c d, { fst := extent_closure r (intent_closure r $ c.fst ∪ d.fst),
  snd := c.snd ∩ d.snd,
  closure_fst := begin
    ext, simp, rw [c.closure_fst, d.closure_fst], sorry
  end,
  closure_snd := _ }⟩

instance : complete_lattice (concept α β r) := sorry

variables {α β γ}

def derived_le [has_le γ] (f : α → γ) (g : β → γ) (a : α) (b : β) : Prop := f a ≤ g b

-- Also requires `range f` to be `⊔`-dense and `range g` to be `⊓`-dense.
/-- A complete lattice is isomorphic to some concept lattice. -/
def order_iso.concept [complete_lattice γ] (f : α → γ) (g : β → γ) :
  γ ≃o concept α β (derived_le f g) := sorry

/-- A complete lattice is isomorphic to its concept lattice of `≤`. -/
def order_iso.concept_le [complete_lattice α] : α ≃o concept α α (≤) := order_iso.concept id id
