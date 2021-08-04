/-
Copyright (c) 2021 Yaël Dillies, Kendall Frey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kendall Frey
-/
import data.set.basic

class circular_preorder (α : Type*) :=
(between : α → α → α → Prop)
(cyclic : ∀ a b c : α, between a b c → between b c a)
(trans : ∀ a b c d : α, between a b c → between a c d → between a b d)

export circular_preorder (between)

class circular_partial_order (α : Type*) extends circular_preorder α :=
(antisymm : ∀ a b c : α, between a b c → between a c b → b = c)

class circular_order (α : Type*) extends circular_partial_order α :=
(total : ∀ a b c : α, between a b c ∨ between a c b)

section circular_preorder
variables {α : Type*} [circular_preorder α]

/-- Circular interval closed-closed -/
def cIcc (a b : α) : set α := {x | between a x b}

/-- Circular interval closed-open -/
def cIco (a b : α) : set α := {x | between a x b ∧ ¬between a b x}

/-- Circular interval open-closed -/
def cIoc (a b : α) : set α := {x | between a x b ∧ ¬between x a b}

/-- Circular interval open-open -/
def cIoo (a b : α) : set α := {x | between a x b ∧ ¬between a b x ∧ ¬between x a b}

end circular_preorder
