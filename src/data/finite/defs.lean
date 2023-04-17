/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import logic.equiv.basic

/-!
# Definition of the `finite` typeclass

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a typeclass `finite` saying that `α : Sort*` is finite. A type is `finite` if it
is equivalent to `fin n` for some `n`. We also define `infinite α` as a typeclass equivalent to
`¬finite α`.

The `finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite.  While the `fintype` class also
represents finiteness of a type, a key difference is that a `fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `fintype` instances.

Every `fintype` instance automatically gives a `finite` instance, see `fintype.finite`, but not vice
versa. Every `fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `fintype` instance, one should prefer writing a `finite` instance
instead.

## Main definitions

* `finite α` denotes that `α` is a finite type.
* `infinite α` denotes that `α` is an infinite type.

## Implementation notes

The definition of `finite α` is not just `nonempty (fintype α)` since `fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `finite.prop`.

## Tags

finite, fintype
-/

universes u v
open function
variables {α β : Sort*}

/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class inductive finite (α : Sort*) : Prop
| intro {n : ℕ} : α ≃ fin n → finite

lemma finite_iff_exists_equiv_fin {α : Sort*} : finite α ↔ ∃ n, nonempty (α ≃ fin n) :=
⟨λ ⟨e⟩, ⟨_, ⟨e⟩⟩, λ ⟨n, ⟨e⟩⟩, ⟨e⟩⟩

lemma finite.exists_equiv_fin (α : Sort*) [h : finite α] : ∃ (n : ℕ), nonempty (α ≃ fin n) :=
finite_iff_exists_equiv_fin.mp h

lemma finite.of_equiv (α : Sort*) [h : finite α] (f : α ≃ β) : finite β :=
by { casesI h with n e, exact finite.intro (f.symm.trans e) }

lemma equiv.finite_iff (f : α ≃ β) : finite α ↔ finite β :=
⟨λ _, by exactI finite.of_equiv _ f, λ _, by exactI finite.of_equiv _ f.symm⟩

lemma function.bijective.finite_iff {f : α → β} (h : bijective f) : finite α ↔ finite β :=
(equiv.of_bijective f h).finite_iff

lemma finite.of_bijective [finite α] {f : α → β} (h : bijective f) : finite β := h.finite_iff.mp ‹_›

instance [finite α] : finite (plift α) := finite.of_equiv α equiv.plift.symm
instance {α : Type v} [finite α] : finite (ulift.{u} α) := finite.of_equiv α equiv.ulift.symm

/-- A type is said to be infinite if it is not finite. Note that `infinite α` is equivalent to
`is_empty (fintype α)` or `is_empty (finite α)`. -/
class infinite (α : Sort*) : Prop :=
(not_finite : ¬finite α)

@[simp] lemma not_finite_iff_infinite : ¬finite α ↔ infinite α := ⟨infinite.mk, λ h, h.1⟩

@[simp] lemma not_infinite_iff_finite : ¬infinite α ↔ finite α :=
not_finite_iff_infinite.not_right.symm

lemma equiv.infinite_iff (e : α ≃ β) : infinite α ↔ infinite β :=
not_finite_iff_infinite.symm.trans $ e.finite_iff.not.trans not_finite_iff_infinite

instance [infinite α] : infinite (plift α) := equiv.plift.infinite_iff.2 ‹_›
instance {α : Type v} [infinite α] : infinite (ulift.{u} α) := equiv.ulift.infinite_iff.2 ‹_›

lemma finite_or_infinite (α : Sort*) : finite α ∨ infinite α :=
or_iff_not_imp_left.2 $ not_finite_iff_infinite.1

lemma not_finite (α : Sort*) [infinite α] [finite α] : false := @infinite.not_finite α ‹_› ‹_›

protected lemma finite.false [infinite α] (h : finite α) : false := not_finite α
protected lemma infinite.false [finite α] (h : infinite α) : false := not_finite α

alias not_infinite_iff_finite ↔ finite.of_not_infinite finite.not_infinite
