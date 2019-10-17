/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen
-/

import tactic.suggest

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_suggest true

open tactic

--suggest fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { suggest },
end

example (a : Prop) : a ∨ true :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact or.inr trivial"), exact or.inr trivial,
end

example {a a' : ℕ} (h : a == a') : a = a' :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact eq_of_heq h"), exact eq_of_heq h,
end
example {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ "exact eq.trans h₁ h₂" ∈ s), exact eq.trans h₁ h₂,
end

example (n : nat) : n + 0 = n :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact rfl"), exact rfl,
end

example (n : nat) : n < n + 1 :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact nat.lt.base n"),
  exact nat.lt.base n
end
example (n : nat) : n < n + 2 :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ "refine nat.lt.step _" ∈ s),
  refine nat.lt.step _, -- this wasn't the first result; humans still necessary :-(
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact nat.lt.base n"),
  exact nat.lt.base n
end

example (a b : Prop) : (a ∨ true) ∧ (b ∨ true) :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ "refine ⟨_, _⟩" ∈ s),
  refine ⟨_, _⟩, -- wasn't the first result, because it created two new goals
  { (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact or.inr trivial"),
    exact or.inr trivial },
  { (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact or.inr trivial"),
    exact or.inr trivial },
end

example (A B : Prop) (a : A) (b : unit → B) : A ∧ B :=
begin
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "refine ⟨a, _⟩"),
  refine ⟨a, _⟩,
  replace b := b (),
  (do s ← list.map prod.snd <$> suggest, guard $ s.head = "exact b"),
  exact b,
end
