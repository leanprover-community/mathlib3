/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
import logic.basic

universe u

open tactic

namespace nat

/- successor and predecessor -/

theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
or_of_not_implies $ λ H,
(succ_pred_eq_of_pos (nat.pos_of_ne_zero H)).symm

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
⟨_, (succ_pred_eq_of_pos (nat.pos_of_ne_zero H)).symm⟩

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m :=
nat.succ.inj_arrow H id

theorem discriminate {B : Type _} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
by ginduction n with h; [exact H1 h, exact H2 _ h]

theorem one_succ_zero : 1 = succ 0 := rfl
--local attribute [simp] one_succ_zero

theorem two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : Π (a : ℕ), P a
| 0               := H1
| 1               := H2
| (succ (succ n)) := H3 _ (two_step_induction _) (two_step_induction _)

theorem sub_induction {P : ℕ → ℕ → Sort u} (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : Π (n m : ℕ), P n m
| 0        m        := H1 _
| (succ n) 0        := H2 _
| (succ n) (succ m) := H3 _ _ (sub_induction n m)

/- addition -/

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
by simp [succ_add, add_succ]

theorem eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
⟨nat.eq_zero_of_add_eq_zero_right H, nat.eq_zero_of_add_eq_zero_left H⟩

theorem add_one (n : ℕ) : n + 1 = succ n := rfl

theorem one_add (n : ℕ) : 1 + n = succ n := by simp

end nat

section
open nat
def iterate {A : Type} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f`^[`n`]` := iterate f n
end
