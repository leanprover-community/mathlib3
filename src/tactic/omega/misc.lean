/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Miscellaneous. -/

import tactic.localized

variables {α β γ : Type}

namespace omega

lemma fun_mono_2 {p : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 = p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2 {p : α → β → Prop} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2' {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} :
  (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
λ h1 h2, by rw [h1, h2]

/-- Update variable assignment for a specific variable
    and leave everything else unchanged -/
def update (m : nat) (a : α) (v : nat → α) : nat → α
| n := if n = m then a else v n

localized "notation v ` ⟨` m ` ↦ ` a `⟩` := omega.update m a v" in omega

lemma update_eq (m : nat) (a : α) (v : nat → α) : (v ⟨m ↦ a⟩) m = a :=
by simp only [update, if_pos rfl]

lemma update_eq_of_ne {m : nat} {a : α} {v : nat → α} (k : nat) :
  k ≠ m → update m a v k = v k :=
by {intro h1, unfold update, rw if_neg h1}

/-- Assign a new value to the zeroth variable, and push all
    other assignments up by 1 -/
def update_zero (a : α) (v : nat → α) : nat → α
| 0     := a
| (k+1) := v k

open tactic

/-- Intro with a fresh name -/
meta def intro_fresh : tactic unit :=
do n ← mk_fresh_name,
   intro n,
   skip

/-- Revert an expr if it passes the given test -/
meta def revert_cond (t : expr → tactic unit) (x : expr) : tactic unit :=
(t x >> revert x >> skip) <|> skip

/-- Revert all exprs in the context that pass the given test -/
meta def revert_cond_all (t : expr → tactic unit) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip

/-- Try applying a tactic to each of the element in a list
    until success, and return the first successful result -/
meta def app_first {α β : Type} (t : α → tactic β) : list α → tactic β
| [] := failed
| (a :: as) := t a <|> app_first as

end omega
