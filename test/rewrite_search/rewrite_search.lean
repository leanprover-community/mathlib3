/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.rewrite_search
import data.rat.basic
import data.real.basic

/-
These tests ensure that `rewrite_search` works on some relatively simple examples.
They do not monitor for performance regression, so be aware of that if you make changes.
-/

namespace tactic.rewrite_search.testing

private axiom foo' : [6] = [7]
private axiom bar' : [[5], [5]] = [[6], [6]]

example : [[7], [6]] = [[5], [5]] :=
begin
  success_if_fail { rewrite_search },
  rewrite_search [foo', bar']
end

@[rewrite] private axiom foo : [0] = [1]
@[rewrite] private axiom bar1 : [1] = [2]
@[rewrite] private axiom bar2 : [3] = [2]
@[rewrite] private axiom bar3 : [3] = [4]

private example : [[0], [0]] = [[4], [4]] := by rewrite_search
private example (x : unit) : [[0], [0]] = [[4], [4]] := by rewrite_search

@[rewrite] private axiom qux' : [[1], [2]] = [[6], [7]]
@[rewrite] private axiom qux'' : [6] = [7]
private example : [[1], [1]] = [[7], [7]] := by rewrite_search

constants f g : ℕ → ℕ → ℕ → ℕ
@[rewrite] axiom f_0_0 : ∀ a b c : ℕ, f a b c = f 0 b c
@[rewrite] axiom f_0_1 : ∀ a b c : ℕ, f a b c = f 1 b c
@[rewrite] axiom f_0_2 : ∀ a b c : ℕ, f a b c = f 2 b c
@[rewrite] axiom f_1_0 : ∀ a b c : ℕ, f a b c = f a 0 c
@[rewrite] axiom f_1_1 : ∀ a b c : ℕ, f a b c = f a 1 c
@[rewrite] axiom f_1_2 : ∀ a b c : ℕ, f a b c = f a 2 c
@[rewrite] axiom f_2_0 : ∀ a b c : ℕ, f a b c = f a b 0
@[rewrite] axiom f_2_1 : ∀ a b c : ℕ, f a b c = f a b 1
@[rewrite] axiom f_2_2 : ∀ a b c : ℕ, f a b c = f a b 2
@[rewrite] axiom g_0_0 : ∀ a b c : ℕ, g a b c = g 0 b c
@[rewrite] axiom g_0_1 : ∀ a b c : ℕ, g a b c = g 1 b c
@[rewrite] axiom g_0_2 : ∀ a b c : ℕ, g a b c = g 2 b c
@[rewrite] axiom g_1_0 : ∀ a b c : ℕ, g a b c = g a 0 c
@[rewrite] axiom g_1_1 : ∀ a b c : ℕ, g a b c = g a 1 c
@[rewrite] axiom g_1_2 : ∀ a b c : ℕ, g a b c = g a 2 c
@[rewrite] axiom g_2_0 : ∀ a b c : ℕ, g a b c = g a b 0
@[rewrite] axiom g_2_1 : ∀ a b c : ℕ, g a b c = g a b 1
@[rewrite] axiom g_2_2 : ∀ a b c : ℕ, g a b c = g a b 2
@[rewrite] axiom f_g : f 0 1 2 = g 2 0 1

lemma test_pathfinding : f 0 0 0 = g 0 0 0 := by rewrite_search

constant h : ℕ → ℕ
@[rewrite,simp] axiom a1 : h 0 = h 1
@[rewrite,simp] axiom a2 : h 1 = h 2
@[rewrite,simp] axiom a3 : h 2 = h 3
@[rewrite,simp] axiom a4 : h 3 = h 4

lemma test_linear_path : h 0 = h 4 := by rewrite_search

constants a b c d e : ℚ

lemma test_algebra : (a * (b + c)) * d = a * (b * d) + a * (c * d) :=
by rewrite_search [add_comm, add_assoc, mul_assoc, mul_comm, left_distrib, right_distrib]

lemma test_simpler_algebra : a + (b + c) = (a + b) + c :=
by rewrite_search [add_assoc]

def idf : ℝ → ℝ := id

/-
These problems test `rewrite_search`'s ability to carry on in the presence of multiple
expressions that `pp` to the same thing but are not actually equal.
-/
lemma test_pp_1 : idf (0 : ℕ) = idf (0 : ℚ) :=
by rewrite_search [rat.cast_zero, nat.cast_zero, add_comm]

lemma test_pp_2 : idf (0 : ℕ) + 1 = 1 + idf (0 : ℚ) :=
by rewrite_search [rat.cast_zero, nat.cast_zero, add_comm]

example (x : ℕ) : x = x := by rewrite_search

end tactic.rewrite_search.testing
