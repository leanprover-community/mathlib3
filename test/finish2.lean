/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Nathaniel Thomas
-/
import tactic.finish

/-!
# More examples to test `finish`

Shamelessly stolen by Jeremy from Nathaniel's `tauto`.
-/

open nat

section

variables (a b c d e f : Prop)
variable even : ℕ → Prop
variable P : ℕ → Prop

-- these next five are things that tauto doesn't get

example : (∀ x, P x) ∧ b → (∀ y, P y) ∧ P 0 ∨ b ∧ P 0 := by finish
example : (∀ A, A ∨ ¬A) → ∀ x y : ℕ, x = y ∨ x ≠ y := by finish
example : ∀ b1 b2, b1 = b2 ↔ (b1 = tt ↔ b2 = tt) := begin intro b1, cases b1; finish [iff_def] end

example : ∀ (P Q : nat → Prop), (∀ n, Q n → P n) → (∀ n, Q n) → P 2 := by finish
example (a b c : Prop) : ¬ true ∨ false ∨ b ↔ b := by finish

example : true := by finish

example : false → a := by finish
example : a → a := by finish
example : (a → b) → a → b := by finish
example : ¬ a → ¬ a := by finish
example : a → (false ∨ a) := by finish
example : (a → b → c) → (a → b) → a → c := by finish
example : a → ¬ a → (a → b) → (a ∨ b) → (a ∧ b) → a → false := by finish
example : ((a ∧ b) ∧ c) → b := by finish
example : ((a → b) → c) → b → c := by finish
example : (a ∨ b) → (b ∨ a) := by finish
example : (a → b ∧ c) → (a → b) ∨ (a → c) := by finish
example : ∀ (x0 : a ∨ b) (x1 : b ∧ c), a → b := by finish
example : a → b → (c ∨ b) := by finish
example : (a ∧ b → c) → b → a → c := by finish
example : (a ∨ b → c) → a → c := by finish
example : (a ∨ b → c) → b → c := by finish
example : (a ∧ b) → (b ∧ a) := by finish
example : (a ↔ b) → a → b := by finish
example : a → ¬¬a := by finish
example : ¬¬(a ∨ ¬a) := by finish
example : ¬¬(a ∨ b → a ∨ b) := by finish
example : ¬¬((∀ n, even n) ∨ ¬(∀ m, even m)) := by finish
example : (¬¬b → b) → (a → b) → ¬¬a → b := by finish
example : (¬¬b → b) → (¬b → ¬ a) → ¬¬a → b := by finish

example : ((a → b → false) → false) → (b → false) → false := by finish

example : ((((c → false) → a) → ((b → false) → a) → false) → false) →
            (((c → b → false) → false) → false) → ¬a → a := by finish

example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by finish
example : ∀ (F F' : Prop), F ∧ F' → F := by finish
example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 := by finish
example : ∀ (f : nat → Prop), f 2 → ∃ x, f x := by finish
example : true ∧ true ∧ true ∧ true ∧ true ∧ true ∧ true := by finish
example : ∀ (P : nat → Prop), P 0 → (P 0 → P 1) → (P 1 → P 2) → (P 2) := by finish
example : ¬¬¬¬¬a → ¬¬¬¬¬¬¬¬a → false := by finish
example : ∀ n, ¬¬(even n ∨ ¬even n) := by finish
example : ∀ (p q r s : Prop) (a b : nat), r ∨ s → p ∨ q → a = b → q ∨ p := by finish
example : (∀ x, P x) → (∀ y, P y) := by finish

/- TODO(Jeremy): reinstate after simp * at * bug is fixed.
example : ((a ↔ b) → (b ↔ c)) → ((b ↔ c) → (c ↔ a)) → ((c ↔ a) → (a ↔ b)) → (a ↔ b) :=
by finish [iff_def]
-/

example : ((¬a ∨ b) ∧ (¬b ∨ b) ∧ (¬a ∨ ¬b) ∧ (¬b ∨ ¬b) → false) → ¬((a → b) → b) → false :=
by finish

example : ¬((a → b) → b) → ((¬b ∨ ¬b) ∧ (¬b ∨ ¬a) ∧ (b ∨ ¬b) ∧ (b ∨ ¬a) → false) → false :=
by finish

example : (¬a ↔ b) → (¬b ↔ a) → (¬¬a ↔ a) := by finish

example : (¬ a ↔ b) → (¬ (c ∨ e) ↔ d ∧ f) → (¬ (c ∨ a ∨ e) ↔ d ∧ b ∧ f) := by finish

example {A : Type} (p q : A → Prop) (a b : A) : q a → p b → ∃ x, (p x ∧ x = b) ∨ q x := by finish

example {A : Type} (p q : A → Prop) (a b : A) : p b → ∃ x, q x ∨ (p x ∧ x = b) := by finish

example : ¬ a → b → a → c := by finish
example : a → b → b → ¬ a → c := by finish
example (a b : nat) : a = b → b = a := by finish

-- good examples of things we don't get, even using the simplifier
example (a b c : nat) : a = b → a = c → b = c := by finish
example (p : nat → Prop) (a b c : nat) : a = b → a = c → p b → p c := by finish

example (p : Prop) (a b : nat) : a = b → p → p := by finish

-- safe should look for contradictions with constructors
example (a : nat) : (0 : ℕ) = succ a → a = a → false := by finish
example (p : Prop) (a b c : nat) : [a, b, c] = [] → p := by finish

example (a b c : nat) : succ (succ a) = succ (succ b) → c = c := by finish
example (p : Prop) (a b : nat) : a = b → b ≠ a → p := by finish
example : (a ↔ b) → ((b ↔ a) ↔ (a ↔ b)) := by finish
example (a b c : nat) : b = c → (a = b ↔ c = a) := by finish [iff_def]
example : ¬¬¬¬¬¬¬¬a → ¬¬¬¬¬a → false := by finish
example (a b c : Prop) : a ∧ b ∧ c ↔ c ∧ b ∧ a := by finish
example (a b c : Prop) : a ∧ false ∧ c ↔ false := by finish
example (a b c : Prop) : a ∨ false ∨ b ↔ b ∨ a := by finish
example : a ∧ not a ↔ false := by finish
example : a ∧ b ∧ true → b ∧ a := by finish
example (A : Type) (a₁ a₂ : A) : a₁ = a₂ →
  (λ (B : Type) (f : A → B), f a₁) = (λ (B : Type) (f : A → B), f a₂) := by finish
example (a : nat) : ¬ a = a → false := by finish
example (A : Type) (p : Prop) (a b c : A) : a = b → b ≠ a → p := by finish
example (p q r s : Prop) : r ∧ s → p ∧ q → q ∧ p := by finish
example (p q : Prop) : p ∧ p ∧ q ∧ q → q ∧ p := by finish
example (p : nat → Prop) (q : nat → nat → Prop) :
  (∃ x y, p x ∧ q x y) → q 0 0 ∧ q 1 1 → (∃ x, p x) := by finish
example (p q r s : Prop) (a b : nat) : r ∨ s → p ∨ q → a = b → q ∨ p := by finish
example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by finish
example (a b : Prop) : a → b → a := by finish
example (p q : nat → Prop) (a b : nat) : p a → q b → ∃ x, p x := by finish

example : ∀ b1 b2, b1 && b2 = ff ↔ (b1 = ff ∨ b2 = ff) := by finish
example : ∀ b1 b2, b1 && b2 = tt ↔ (b1 = tt ∧ b2 = tt) := by finish
example : ∀ b1 b2, b1 || b2 = ff ↔ (b1 = ff ∧ b2 = ff) := by finish
example : ∀ b1 b2, b1 || b2 = tt ↔ (b1 = tt ∨ b2 = tt) := by finish
example : ∀ b, bnot b = tt ↔ b = ff := by finish
example : ∀ b, bnot b = ff ↔ b = tt := by finish
example : ∀ b c, b = c ↔ ¬ (b = bnot c) := by intros b c; cases b; cases c; finish [iff_def]

inductive and3 (a b c : Prop) : Prop
| mk : a → b → c → and3

example (h : and3 a b c) : and3 b c a := by cases h; split; finish

inductive or3 (a b c : Prop) : Prop
| in1 : a → or3
| in2 : b → or3
| in3 : c → or3

/- TODO(Jeremy): write a tactic that tries all constructors
example (h : a) : or3 a b c := sorry
example (h : b) : or3 a b c := sorry
example (h : c) : or3 a b c := sorry
-/

variables (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop)
-- H first, all pos

example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) : B₄ := by finish
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄) : B₃ := by finish
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄) : B₂ := by finish
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : B₁ := by finish

example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₃ := by finish
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₂ := by finish
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₁ := by finish

-- H last, all pos
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₄ := by finish
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₃ := by finish
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₂ := by finish
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₁ := by finish

example (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₃ := by finish
example (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₂ := by finish
example (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₁ := by finish

-- H first, all neg
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) : ¬B₄ := by finish
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) : ¬B₃ := by finish
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) : ¬B₂ := by finish
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬B₁ := by finish

example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₃ := by finish
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₂ := by finish
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₁ := by finish

-- H last, all neg
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₄ := by finish
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₃ := by finish
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₂ := by finish
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₁ := by finish

example (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₃ := by finish
example (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₂ := by finish
example (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₁ := by finish

section club
variables Scottish RedSocks WearKilt Married GoOutSunday : Prop
theorem NoMember : (¬Scottish → RedSocks) → (WearKilt ∨ ¬RedSocks) → (Married → ¬GoOutSunday) →
                 (GoOutSunday ↔ Scottish) → (WearKilt → Scottish ∧ Married) →
                 (Scottish → WearKilt) → false := by finish
end club

end
