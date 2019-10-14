-- Copyright (c) 2019 Lucas Allen. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Lucas Allen

import tactic.refine_list

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_refine_list true

open tactic

--refine_list fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { refine_list },
end

example (a : Prop) : a ∨ true :=
begin
  refine_list, exact or.inr trivial,
end

example {a a' : ℕ} (h : a == a') : a = a' :=
begin
  refine_list, exact eq_of_heq h,
end
example {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  refine_list, exact eq.trans h₁ h₂,
end

example (n : nat) : n + 0 = n :=
begin
  refine_list, exact rfl,
end

example (n : nat) : n < n + 1 :=
begin
  refine_list,
  exact nat.lt.base n
end
example (n : nat) : n < n + 2 :=
begin
  refine_list,
  refine nat.lt.step _, -- this wasn't the first result; humans still necessary :-(
  refine_list,
  exact nat.lt.base n
end

example (a b : Prop) : (a ∨ true) ∧ (b ∨ true) :=
begin
  refine_list,
  refine ⟨_, _⟩, -- wasn't the first result, because it created two new goals
  refine_list,
  exact or.inr trivial,
  refine_list,
  exact or.inr trivial,
end

example (A B : Prop) (a : A) (b : unit → B) : A ∧ B :=
begin
  refine_list,
  refine ⟨a, _⟩,
  replace b := b (),
  refine_list,
  exact b,
end
