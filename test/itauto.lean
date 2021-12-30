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

example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
example (p : Prop) : ¬ (p = ¬ p) := by itauto
example (p : Prop) : p ≠ ¬ p := by itauto

example (p : Prop) : p ∧ true ↔ p := by itauto
example (p : Prop) : p ∨ false ↔ p := by itauto
example (p q : Prop) (h0 : q) : p → q := by itauto
example (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q r : Prop) (h : p) : (p → q ∨ r) → q ∨ r := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by itauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : false := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) : p ↔ r := by itauto
example (p q : Prop) : xor p q → (p ↔ ¬ q) := by itauto
example (p q : Prop) : xor p q → xor q p := by itauto

example (p q r : Prop) (h : ¬ (p ↔ q)) (h' : r ↔ q) : ¬ (p ↔ r) := by itauto

example (p : Prop) : p → ¬ (p → ¬ p) := by itauto

example (p : Prop) (em : p ∨ ¬ p) : ¬ (p ↔ ¬ p) := by itauto

example (p : Prop) [decidable p] : p ∨ ¬ p := by itauto*
example (p : Prop) [decidable p] : ¬ (p ↔ ¬ p) := by itauto
example (p q r : Prop) [decidable p] : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by itauto*
example (p q r : Prop) [decidable q] : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by itauto [q]

example (xl yl zl xr yr zr : Prop) :
  (xl ∧ yl ∨ xr ∧ yr) ∧ zl ∨ (xl ∧ yr ∨ xr ∧ yl) ∧ zr ↔
    xl ∧ (yl ∧ zl ∨ yr ∧ zr) ∨ xr ∧ (yl ∧ zr ∨ yr ∧ zl) :=
by itauto

example : 0 < 1 ∨ ¬ 0 < 1 := by itauto*
example (p : Prop) (h : 0 < 1 → p) (h2 : ¬ 0 < 1 → p) : p := by itauto*

example (b : bool) : ¬ b ∨ b := by itauto*
example (p : Prop) : ¬ p ∨ p := by itauto! [p]
example (p : Prop) : ¬ p ∨ p := by itauto!*

-- failure tests
example (p q r : Prop) : true :=
begin
  have : p ∨ ¬ p, {success_if_fail {itauto}, sorry}, clear this,
  have : ¬ (p ↔ q) → ¬ p → q, {success_if_fail {itauto}, sorry}, clear this,
  have : ¬ (p ↔ q) → (r ↔ q) → (p ↔ ¬ r), {success_if_fail {itauto}, sorry}, clear this,
  trivial
end

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
