/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Miscellaneous.
-/

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

def update (m : nat) (a : α) (v : nat → α) : nat → α
| n := if n = m then a else v n

local notation v `⟨` m `↦` a `⟩` := update m a v

lemma update_eq (m : nat) (a : α) (v : nat → α) : (v ⟨m ↦ a⟩) m = a :=
by simp only [update, if_pos rfl]

lemma update_eq_of_ne {m : nat} {a : α} {v : nat → α} (k : nat) :
  k ≠ m → update m a v k = v k :=
by {intro h1, unfold update, rw if_neg h1} 

def update_zero (a : α) (v : nat → α) : nat → α
| 0     := a
| (k+1) := v k

end omega 