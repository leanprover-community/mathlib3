/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import tactic.finish

/-!
# Examples to test `finish`

The designations "clarify," "safe," "iauto," etc. are from a previous tableau prover.
-/
open auto

section
variables A B C D : Prop

/- clarify -/

example (H : ¬ A) (H' : A) : C := by finish
example (H₁ : A ∧ A ∧ B) (H₂ : A ∧ C ∧ B) : A := by finish

/- safe -/

example (H : A) (H₁ : ¬ B) : ¬ (A → B) := by finish
example : A ∨ B → B ∨ A := by finish
example : A ∧ B → B ∧ A := by finish
example (H : A) (H₁ : A → B) (H₂ : B → C) : C := by finish
example (H₁ : A ∧ B) (H₂ : C ∧ B) : C := by finish
example (HA : A) (HB : B) (HC : C) (HD : D) : (A ∧ B) ∧ (C ∧ D) := by finish
example (H₁ : A ∧ B) (H₂ : B ∧ ¬ C) : A ∨ C := by finish
example : (A → B) ∧ (B → C) → A → C := by finish
example : (A → B) ∨ (B → A) := by finish
example : ((A → B) → A) → A := by finish

/- iauto -/

example (H : A) (H₁ : ¬ B) : ¬ (A → B) := by finish
example : ¬ (A ↔ ¬ A) := by finish
example (H : A ↔ B) (H₁ : A ∧ B → C) (H₂ : ¬ A ∧ ¬ B → C) : C := by finish
example (H : A ↔ B) (H₁ : (A ∧ ¬ B) ∨ (¬ A ∧ B)) : C := by finish
example (H : A → B) (H₁ : A) : B := by finish
example (H : A → B) (H₁ : B → C) : A → C := by finish
example (H : A → B ∨ C) (H₁ : B → D) (H₂ : C → D) : A → D := by finish
example : A ∨ B → B ∨ A := by finish

/- using injectivity -/

section
open nat

example (x y : ℕ) : succ x = succ y → x = y ∨ x = succ y := by finish
example (x y z : ℕ) : succ (succ x) = succ y ∧ y = succ z →
  y = succ x ∧ succ x = succ z :=
by finish

end

/-
-- Examples with quantifiers
-/

section
variables (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X)

/- auto -/

example (H : ∀ x, P x → Q x) (H₁ : ∀ x, P x) : Q a := by finish
example (H : ∀ x, P x → Q x) (H₁ : P a) : Q a := by finish

/- iauto -/

example (H₁ : P a) (H₂ : P b) : ∃ x, P x := by finish
example (H₁ : P a) (H₂ : P b) (H₃ : Q b) : ∃ x, P x ∧ Q x := by finish
example (H₁ : P b) (H₂ : Q b) (H₃ : P a) : ∃ x, P x ∧ Q x := by finish
example (H : ∀ x, P x → Q x ∧ R x) (a : X) (H₁ : P a) : R a ∧ Q a := by finish
example (H : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by finish

-- not valid in dependent type theory!
-- example : ∃ x, ((∃ y, P y) → P x) :=
-- by auto'

/- Beyond the scope of finish.
example (H : ∃ x : X, x = x) : ∃ x, ((∃ y, P y) → P x) := by finish
example : (∃ x, ∀ y, T x y) → ∀ y, ∃ x, T x y := by finish
-/

end

example (x y z : ℕ) (p : ℕ → Prop) (h₀ : x = y) (h₁ : y = z) (h₂ : ∀ w, w = z → p w) : p x :=
by finish

end

/-
  more examples
-/


constant foo : Prop
axiom not_foo : ¬ foo

section

variables a b c d : Prop

example : a ∧ b → a := by finish
example : a → (a → b) → (b → c) ∧ (d → ¬ c) → ¬ d := by finish

example : a ∨ b → b ∨ a := by finish

example : ¬ (a ↔ ¬ a) :=
begin
  finish
end

/- examples of tactics that leave goals -/

/-
example : a ∨ b ∨ foo → b ∨ a :=
begin
  clarify,
  admit
end

example : a ∨ b ∨ foo ∨ foo → b ∨ a :=
begin
  safe,
  admit
end

example : a ∨ b ∨ c → ¬ a → ¬ b → d :=
begin
  safe,
  admit
end
-/

end

section

variables (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, p x) : q a :=
by finish

example (h₁ : p a) : ∃ x, p x :=
by finish

example (h₁ : p a) (h₂ : p b) (h₃ : q b) : ∃ x, p x ∧ q x :=
by finish

example (h : ∃ x, p x ∧ r x x) (h' : ∀ x, r x x → q x) : ∃ x, p x ∧ q x :=
by finish

example (h : ∃ x, q x ∧ p x)  : ∃ x, p x ∧ q x :=
by finish

example (h₁ : ∀ x, q x → p x) (h₃ : q a)  : ∃ x, p x :=
by finish

example (h₁ : ∀ x, p x → q x → false) (h₂ : p a) (h₃ : p b) (h₄ : q b) : false :=
by finish

example (h : ∀ x, p x) (h₁ : ∀ x, p x → q x) : ∀ x, q x :=
by finish

example (h : ∃ x, p x) (h₁ : ∀ x, p x → q x) : ∃ x, q x :=
by finish

example (h : ¬ ∀ x, ¬ p x) (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, ¬ q x) : false :=
by finish

/-
example (h : p a) (h' : p a → false) : false :=
by finish
-/

end

section
  variables a b c d : Prop
  variables (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)

  example (h : ¬ ∀ x, (∃ y, r x y) → p x) : true :=
  begin
    normalize_hyps {},
    trivial
  end

  example (h₁ : a → b ∨ c) (h₂ : ¬ b) : a → c :=
  begin
    simp * at *,
    assumption
  end
end
