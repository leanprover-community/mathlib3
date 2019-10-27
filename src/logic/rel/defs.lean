/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Yury Kudryashov
-/
import logic.function

/-!
# Definitions of a relation, its domain, range, (pre)image of a set etc.

In this file we define `rel α β` to be `α → β → Prop`, and define:

* the graph of a function `f : α → β` (both as a relation and as a set in `α × β`);
* the graph of a relation;
* the domain and range of a relation;
* the (pre)image of a set by a relation;
* the converse relation (aka `flip`), and the diagonal of a relation;
* (co)map₂, (co)map;
* (left/right/bi)_(unique/total) relations;
* two ways to lift a pair of relations to a relation on functions.

We prove no properties in this file to avoid circular `import`s.

## Notation

`r₁ ⇒ r₂` is used for the following relation on functions:
`(r₁ ⇒ r₂) f g ↔ ∀ x y, r₁ x y → r₂ (f x) (f y)`
-/

universes u v w x

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
def rel (α : Sort u) (β : Sort v) := α → β → Prop

reserve infixr ` ⇒ `:40

/-- Graph of a function as a relation. -/
def function.to_rel {α : Sort u} {β : Sort v} (f : α → β) : rel α β := λ x y, f x = y

namespace rel

section sort

variables {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (r : rel α β)

/-- The identity relation: `id α x y = (x = y)`. -/
protected def id (α) : rel α α := @eq α

/-- The converse relation : `r.flip x y ↔ r y x` -/
protected def flip : rel β α := flip r

/-- Composition of relations -/
def comp (r : rel β γ) (s : rel α β) : rel α γ :=
λ x z, ∃ y, r y z ∧ s x y

/-- Restriction of a relation to the diagonal. -/
def diag (r : rel α α) : α → Prop := λ x, r x x

/-- A relation is `left_total`, if its domain is `univ`. -/
def left_total := ∀a, ∃b, r a b
/-- A relation is `right_total`, if its range is `univ`. -/
def right_total := ∀b, ∃a, r a b
/-- A relation is `bi_total`, it it is both `left_total` and `right_total`. -/
def bi_total := left_total r ∧ right_total r

/-- A relation is `left_unique`, if each `b` has at most one preimage. -/
def left_unique := ∀⦃a b c⦄, r a c → r b c → a = b
/-- A relation is `right_unique`, if each `a` has at most one image. -/
def right_unique := ∀⦃a b c⦄, r a b → r a c → b = c
/-- A relation is `bi_unique`, if it is both `left_unique` and `right_unique`. -/
def bi_unique : Prop := left_unique r ∧ right_unique r

/-- Pullback of a relation by a pair of functions.-/
def comap₂ (f : α → β) (g : γ → δ) (r : rel β δ) : rel α γ :=
λ x y, r (f x) (g y)

/-- Pullback of a relation. -/
protected def comap (f : α → β) (r : rel β β) : rel α α := r.comap₂ f f

/-- Pushforward of a relation by a pair of functions. -/
def map₂ (f : α → β) (g : γ → δ) (r : rel α γ) : rel β δ :=
(function.to_rel g).comp $ r.comp (function.to_rel f).flip

/-- Pushforward of a relation -/
protected def map (f : α → β) (r : rel α α) : rel β β := r.map₂ f f

/-- Lift a pair of relations to a relation on functions. -/
def lift_fun (rac : rel α γ) (rbd : rel β δ) : rel (α → β) (γ → δ) :=
λ f g, ∀⦃x y⦄, rac x y → rbd (f x) (g y)

infixr ⇒ := lift_fun

/-- Lift a pair of relation to a relation on functions with reversed implication. -/
def lift_fun_rev (rac : rel α γ) (rbd : rel β δ) : rel (α → β) (γ → δ) :=
λ f g, ∀⦃x y⦄, rbd (f x) (g y) → rac x y

end sort

section type

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} (r : rel α β)

/-- Graph of a relation -/
protected def graph : set (α × β) := { x : α × β | r x.fst x.snd }

/-- Reconstruct a relation by its graph. -/
def of_graph (s : set (α × β)) : rel α β := function.curry s

/-- Domain of a relation -/
def dom : set α := {x | ∃ y, r x y}

/-- Range of a relation. -/
def range : set β := {y | ∃ x, r x y}

/-- Image of a set under a relation -/
def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : set β) : set α := r.flip.image s

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only* to elements of `s`. -/
def core (s : set β) := {x | ∀ ⦃y⦄, r x y → y ∈ s}

/-- Restrict the domain of a relation -/
def restrict (s : set α) : rel α β :=
λ x y, x ∈ s ∧ r x y

end type

end rel

/-- Graph of a function as a set in `α × β`. -/
def function.graph {α : Type u} {β : Type v} (f : α → β) : set (α × β) := (function.to_rel f).graph
