/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.free_monoid.basic
import data.list.count

/-!
# `list.count` as a bundled homomorphism

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `free_monoid.countp`, `free_monoid.count`, `free_add_monoid.countp`, and
`free_add_monoid.count`. These are `list.countp` and `list.count` bundled as multiplicative and
additive homomorphisms from `free_monoid` and `free_add_monoid`.

We do not use `to_additive` because it can't map `multiplicative ℕ` to `ℕ`.
-/

variables {α : Type*} (p : α → Prop) [decidable_pred p]

namespace free_add_monoid

/-- `list.countp` as a bundled additive monoid homomorphism. -/
def countp (p : α → Prop) [decidable_pred p] : free_add_monoid α →+ ℕ :=
⟨list.countp p, list.countp_nil p, list.countp_append _⟩

lemma countp_of (x : α) : countp p (of x) = if p x then 1 else 0 := rfl

lemma countp_apply (l : free_add_monoid α) : countp p l = list.countp p l := rfl

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [decidable_eq α] (x : α) : free_add_monoid α →+ ℕ := countp (eq x)

lemma count_of [decidable_eq α] (x y : α) : count x (of y) = pi.single x 1 y :=
by simp only [count, countp_of, pi.single_apply, eq_comm]

lemma count_apply [decidable_eq α] (x : α) (l : free_add_monoid α) :
  count x l = list.count x l :=
rfl

end free_add_monoid

namespace free_monoid

/-- `list.countp` as a bundled multiplicative monoid homomorphism. -/
def countp (p : α → Prop) [decidable_pred p] : free_monoid α →* multiplicative ℕ :=
(free_add_monoid.countp p).to_multiplicative

lemma countp_of' (x : α) :
  countp p (of x) = if p x then multiplicative.of_add 1 else multiplicative.of_add 0 :=
rfl

lemma countp_of (x : α) : countp p (of x) = if p x then multiplicative.of_add 1 else 1 :=
by rw [countp_of', of_add_zero] -- `rfl` is not transitive

lemma countp_apply (l : free_add_monoid α) :
  countp p l = multiplicative.of_add (list.countp p l) :=
rfl

/-- `list.count` as a bundled additive monoid homomorphism. -/
def count [decidable_eq α] (x : α) : free_monoid α →* multiplicative ℕ := countp (eq x)

lemma count_apply [decidable_eq α] (x : α) (l : free_add_monoid α) :
  count x l = multiplicative.of_add (list.count x l) :=
rfl

lemma count_of [decidable_eq α] (x y : α) :
  count x (of y) = @pi.mul_single α (λ _, multiplicative ℕ) _ _ x (multiplicative.of_add 1) y :=
by simp only [count, countp_of, pi.mul_single_apply, eq_comm]

end free_monoid
