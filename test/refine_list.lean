-- Copyright (c) 2019 Lucas Allen. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Lucas Allen

import tactic.refine_list

/- Turn off trace messages so they don't pollute the test build: -/
--set_option trace.silence_library_search true

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

example (n : nat) : n + 2 > n :=
begin
  refine_list,
end

open nat
