/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.tauto

section tauto₀
variables p q r : Prop
variables h : p ∧ q ∨ p ∧ r
include h
example : p ∧ p :=
by tauto

end tauto₀

section tauto₁
variables α : Type
variables p q r : α → Prop
variables h : (∃ x, p x ∧ q x) ∨ (∃ x, p x ∧ r x)
include h
example : ∃ x, p x :=
by tauto

end tauto₁

section tauto₂
variables α : Type
variables x : α
variables p q r : α → Prop
variables h₀ : (∀ x, p x → q x → r x) ∨ r x
variables h₁ : p x
variables h₂ : q x

include h₀ h₁ h₂
example : ∃ x, r x :=
by tauto

end tauto₂

section tauto₃


example (p : Prop) : p ∧ true ↔ p := by tauto
example (p : Prop) : p ∨ false ↔ p := by tauto
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
example (p q r : Prop) [decidable q] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ p) : q := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) : p := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : false :=
by tauto
example (p q r : Prop) [decidable q] [decidable p] (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p :=
by tauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) : p ↔ r :=
by tauto!

example (p q r : Prop) (h : ¬ p = q) (h' : r = q) : p ↔ ¬ r := by tauto!

example (p : Prop) : p → ¬ (p → ¬ p) := by tauto

example (p : Prop) (em : p ∨ ¬ p) : ¬ (p ↔ ¬ p) := by tauto

example (P : ℕ → Prop) (n : ℕ) : P n → n = 7 ∨ n = 0 ∨ ¬ (n = 7 ∨ n = 0) ∧ P n :=
by tauto

section modulo_symmetry
variables {p q r : Prop} {α : Type} {x y : α}
variables (h : x = y)
variables (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
include h
include h''
example (h' : ¬ y = x) : p ∧ q := by tauto
example (h' : p ∧ ¬ y = x) : p ∧ q := by tauto
example : y = x := by tauto
example (h' : ¬ x = y) : p ∧ q := by tauto
example : x = y := by tauto
end modulo_symmetry

end tauto₃

section closer

example {α : Type*} {β : Type*} (a : α)
  {s_1 : set α} :
  (∃ (a_1 : α), a_1 = a ∨ a_1 ∈ s_1) :=
begin
  tauto {closer := `[simp]}
end

variables {p q r : Prop} {α : Type} {x y z w : α}
variables (h : x = y) (h₁ : y = z) (h₂ : z = w)
variables (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
include h h₁ h₂ h''

example : (((r ∧ p ↔ r ∨ q) ∧ (q ∨ r)) → (p ∧ (x = w) ∧ (¬ x = w → p ∧ q ∧ r))) :=
begin
  tauto {closer := `[cc]}
end

end closer
