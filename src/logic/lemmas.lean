/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import tactic.congr
import tactic.protected
import tactic.rcases
import tactic.split_ifs
import logic.basic

/-!
# More basic logic properties

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A few more logic lemmas. These are in their own file, rather than `logic.basic`, because it is
convenient to be able to use the `split_ifs` tactic.

## Implementation notes

We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/

alias heq_iff_eq ↔ heq.eq eq.heq

attribute [protected] heq.eq eq.heq

alias ne_of_eq_of_ne ← eq.trans_ne
alias ne_of_ne_of_eq ← ne.trans_eq

variables {α : Sort*} {p q r : Prop} [decidable p] [decidable q] {a b c : α}

lemma dite_dite_distrib_left {a : p → α} {b : ¬ p → q → α} {c : ¬ p → ¬ q → α} :
  dite p a (λ hp, dite q (b hp) (c hp)) =
    dite q (λ hq, dite p a $ λ hp, b hp hq) (λ hq, dite p a $ λ hp, c hp hq) :=
by split_ifs; refl

lemma dite_dite_distrib_right {a : p → q → α} {b : p → ¬ q → α} {c : ¬ p → α} :
  dite p (λ hp, dite q (a hp) (b hp)) c =
    dite q (λ hq, dite p (λ hp, a hp hq) c) (λ hq, dite p (λ hp, b hp hq) c) :=
by split_ifs; refl

lemma ite_dite_distrib_left {a : α} {b : q → α} {c : ¬ q → α} :
  ite p a (dite q b c) = dite q (λ hq, ite p a $ b hq) (λ hq, ite p a $ c hq) :=
dite_dite_distrib_left

lemma ite_dite_distrib_right {a : q → α} {b : ¬ q → α} {c : α} :
  ite p (dite q a b) c = dite q (λ hq, ite p (a hq) c) (λ hq, ite p (b hq) c) :=
dite_dite_distrib_right

lemma dite_ite_distrib_left {a : p → α} {b : ¬ p → α} {c : ¬ p → α} :
  dite p a (λ hp, ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
dite_dite_distrib_left

lemma dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬ p → α} :
  dite p (λ hp, ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
dite_dite_distrib_right

lemma ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
dite_dite_distrib_left

lemma ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
dite_dite_distrib_right

lemma Prop.forall {f : Prop → Prop} : (∀ p, f p) ↔ f true ∧ f false :=
⟨λ h, ⟨h _, h _⟩, by { rintro ⟨h₁, h₀⟩ p, by_cases hp : p; simp only [hp]; assumption }⟩

lemma Prop.exists {f : Prop → Prop} : (∃ p, f p) ↔ f true ∨ f false :=
⟨λ ⟨p, h⟩, by refine (em p).imp _ _; intro H; convert h; simp [H], by rintro (h | h); exact ⟨_, h⟩⟩
