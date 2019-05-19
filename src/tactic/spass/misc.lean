/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Miscellaneous.
-/

universe u

variables {α β γ δ : Type u}

def spaces (k : nat) : string := ⟨list.repeat ' ' k⟩

def bool.repr : bool → string
| tt := "tt"
| ff := "ff"

def list.write (f : α → string) (s : string) : list α → string
| []        := ""
| (a :: as) := f a ++ s ++ list.write as

lemma bnot_eq_iff_ne {a b : bool} :
  bnot a = b ↔ a ≠ b :=
by cases a; cases b; simp only
   [bnot, ne, not_false_iff, eq_self_iff_true, not_true]

lemma eq_bnot_iff_ne {a b : bool} :
  a = bnot b ↔ a ≠ b :=
by cases a; cases b; simp only
   [bnot, ne, not_false_iff, eq_self_iff_true, not_true]

lemma ite_cases {r : α → Prop} {p : Prop} [decidable p] {a b : α} :
  r a → r b → r (ite p a b) :=
by { intros h0 h1, by_cases h2 : p,
     { rw if_pos h2, exact h0 },
     rw if_neg h2, exact h1 }

lemma pred_mono_2 {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} :
  (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
λ h1 h2, by rw [h1, h2]

def assign (a : α) (f : nat → α) : nat → α
| 0       := a
| (k + 1) := f k

def digit_to_subs : char → char
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| _ := ' '

def nat.to_subs (n : nat) : string :=
⟨n.repr.data.map digit_to_subs⟩
