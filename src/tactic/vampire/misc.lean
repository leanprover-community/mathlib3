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

meta def bool.to_expr : bool → expr
| ff := `(ff)
| tt := `(tt)

def option.if_is_some (p : α → Prop) : option α → Prop
| none     := true
| (some a) := p a

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

lemma fun_mono_2 {f : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  (a1 = a2) → (b1 = b2) → (f a1 b1 = f a2 b2) :=
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
| _   := ' '

def nat.to_subs (n : nat) : string :=
⟨n.repr.data.map digit_to_subs⟩

namespace nat

  meta def to_expr : nat → expr
  | 0            := `(0)
  | (nat.succ k) := expr.app `(nat.succ) k.to_expr

  lemma succ_lt_succ_iff :
    ∀ {a b : ℕ}, a.succ < b.succ ↔ a < b :=
  begin
    intros a b, apply iff.intro,
    apply lt_of_succ_lt_succ,
    apply succ_lt_succ
  end

  lemma succ_eq_succ_iff (k m : nat) :
    k.succ = m.succ ↔ k = m :=
  by { constructor; intro h0,
       {cases h0, refl}, rw h0 }

  lemma succ_ne_succ {k m : nat} :
    k ≠ m → k.succ ≠ m.succ :=
  by { intros h0 h1, apply h0,
       rwa succ_eq_succ_iff at h1 }

  lemma zero_ne_succ {k : nat} : 0 ≠ k.succ :=
  λ h, by cases h

  -- lemma sub_add_eq_max (k m : nat) : (k - m) + m = max k m :=
  -- begin
  --   by_cases h0 : m ≤ k,
  --   { rw nat.sub_add_cancel h0,
  --     rw max_eq_left h0 },
  --   have h1 := le_of_not_le h0,
  --   simp only [ zero_add, max_eq_right h1,
  --     nat.sub_eq_zero_iff_le.elim_right h1]
  -- end

end nat
