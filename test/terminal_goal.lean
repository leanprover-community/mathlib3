/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.core

open tactic

structure C :=
 ( w : Type )
 ( x : list w )
 ( y : Type )
 ( z : prod w y )

def test_terminal_goal_1 : C :=
 begin
    fapply C.mk, -- We don't just split here, as we want the goals in order.
    success_if_fail { tactic.terminal_goal },
    exact ℕ,
    terminal_goal,
    exact [],
    success_if_fail { terminal_goal },
    exact bool,
    terminal_goal,
    exact (0, tt)
 end

 -- verifying that terminal_goal correctly considers all propositional goals as terminal
structure terminal_goal_struct :=
(x : ℕ)
(p : x = 0)

lemma test_terminal_goal_2 : ∃ F : terminal_goal_struct, F = ⟨ 0, by refl ⟩ :=
begin
  split,
  swap,
  split,
  terminal_goal,
  swap,
  success_if_fail { terminal_goal },
  exact 0,
  refl,
  refl,
end

structure terminal_goal_struct' :=
 ( w : ℕ → Type )
 ( x : list (w 0) )

def test_terminal_goal_3 : terminal_goal_struct' :=
begin
  split,
  swap,
  success_if_fail { terminal_goal },
  intros,
  success_if_fail { terminal_goal },
  exact ℕ,
  exact []
end

def f : unit → Type := λ _, ℕ

def test_terminal_goal_4 : Σ x : unit, f x :=
begin
  split,
  terminal_goal,
  swap,
  terminal_goal,
  exact (),
  dsimp [f],
  exact 0
end

def test_subsingleton_goal_1 : 0 = 0 :=
begin
 subsingleton_goal,
 refl
end

def test_subsingleton_goal_2 : list ℕ :=
begin
 success_if_fail { subsingleton_goal },
 exact []
end
