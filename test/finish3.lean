/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import tactic.finish

/-!
# Examples for `finish`

Those come from the tutorial.
-/

open auto

section
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by finish
example : p ∨ q ↔ q ∨ p := by finish

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by finish
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by finish

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by finish [iff_def]
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by finish [iff_def]

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by finish [iff_def]
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by finish [iff_def]
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by finish
example : ¬p ∨ ¬q → ¬(p ∧ q) := by finish
example : ¬(p ∧ ¬ p) := by finish
example : p ∧ ¬q → ¬(p → q) := by finish
example : ¬p → (p → q) := by finish
example : (¬p ∨ q) → (p → q) := by finish
example : p ∨ false ↔ p := by finish
example : p ∧ false ↔ false := by finish
example : ¬(p ↔ ¬p) := by finish
example : (p → q) → (¬q → ¬p) := by finish

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by finish
example : ¬(p ∧ q) → ¬p ∨ ¬q := by finish
example : ¬(p → q) → p ∧ ¬q := by finish
example : (p → q) → (¬p ∨ q) := by finish
example : (¬q → ¬p) → (p → q) := by finish
example : p ∨ ¬p := by finish
example : (((p → q) → p) → p) := by finish
end


section

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

example : (∃ x : A, r) → r := by finish
-- TODO(Jeremy): can we get these automatically?
example (a : A) : r → (∃ x : A, r) := begin safe; apply_assumption; assumption end
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by finish

theorem foo': (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
by finish [iff_def]

example (h : ∀ x, ¬ ¬ p x) : p a := by finish
example (h : ∀ x, ¬ ¬ p x) : ∀ x, p x := by finish

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by finish

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by finish
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by finish
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by finish
example : (∃ x, ¬ p x) → (¬ ∀ x, p x) := by finish

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by finish [iff_def]
-- TODO(Jeremy): can we get these automatically?
example (a : A) : (∃ x, p x → r) ↔ (∀ x, p x) → r := begin safe [iff_def]; exact h a end
example (a : A) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := begin safe [iff_def]; exact h a end

example : (∃ x, p x → r) → (∀ x, p x) → r := by finish
example : (∃ x, r → p x) → (r → ∃ x, p x) := by finish

end
