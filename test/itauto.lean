/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.itauto

section itauto₀
variables p q r : Prop
variables h : p ∧ q ∨ p ∧ r
include h
example : p ∧ p :=
by itauto

end itauto₀

section itauto₃


example (p : Prop) : p ∧ true ↔ p := by itauto
example (p : Prop) : p ∨ false ↔ p := by itauto
example (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ p) : true :=
by { have : q, success_if_fail {itauto}, sorry, itauto }
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ q) : true :=
by { have : p, success_if_fail {itauto}, sorry, itauto }
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : false := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) : p ↔ r := by itauto

example (p q r : Prop) (h : ¬ (p ↔ q)) (h' : r ↔ q) : true :=
by { have : p ↔ ¬ r, success_if_fail {itauto}, sorry, itauto }
example (p q r : Prop) (h : ¬ (p ↔ q)) (h' : r ↔ q) : ¬ (p ↔ r) := by itauto

example (p : Prop) : p → ¬ (p → ¬ p) := by itauto

example (p : Prop) (em : p ∨ ¬ p) : ¬ (p ↔ ¬ p) := by itauto

example (P : ℕ → Prop) (n : ℕ) (h : ¬ (n = 7 ∨ n = 0) ∧ P n) : ¬ (P n → n = 7 ∨ n = 0) :=
by itauto

section modulo_symmetry
variables {p q r : Prop} {α : Type} {x y : α}
variables (h : x = y)
variables (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
include h
include h''
example (h' : ¬ x = y) : p ∧ q := by itauto
example : x = y := by itauto
end modulo_symmetry

end itauto₃
example (p1 p2 p3 p4 p5 p6 f : Prop)
  (h : (
      (p1 ∧ p2 ∧ p3 ∧ p4 ∧ p5 ∧ p6 ∧ true) ∨
      (((p1 → f) → f) → f) ∨
      (p2 → f) ∨
      (p3 → f) ∨
      (p4 → f) ∨
      (p5 → f) ∨
      (p6 → f) ∨
      false
    ) → f) : f :=
by itauto
