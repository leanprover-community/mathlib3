-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Lucas Allen

import data.nat.basic
import data.nat.prime
import tactic.refine_list

open tactic

--refine_list fails if there are no goals.

example : true :=
begin
  trivial,
  success_if_fail { refine_list },
end

example : true :=
begin
  trivial,
  success_if_fail { refine_list 3 },
end

--These are the basic tests for Library_search, they are being recycled for refine_list.
--refine_list works with no inputs, the maximum length of the list returned will be 50 lines.

example (a b : ℕ) : a + b = b + a :=
begin refine_list, exact add_comm a b, end

example {a b : ℕ} : a ≤ a + b :=
begin refine_list, exact nat.le_add_right a b end

example {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
begin refine_list, exact nat.le_pred_of_lt h end

example {α : Type} (x y : α) : x = y ↔ y = x :=
begin refine_list, exact eq_comm end

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
begin refine_list, exact add_pos ha hb end

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
begin refine_list, exact add_pos, end

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
begin refine_list, exact nat.le_of_dvd w h end

--refine_list can also take a number as input, this gives refine_list an upper bound
--on how many items to return.

example (a b : ℕ) : a + b = b + a :=
begin refine_list 10, exact add_comm a b, end

example {a b : ℕ} : a ≤ a + b :=
begin refine_list 30, exact nat.le_add_right a b end

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
begin refine_list 100, exact nat.mul_sub_left_distrib n m k end

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
begin refine_list 1, exact add_pos, end

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
begin refine_list 15, exact nat.le_of_dvd w h end

example (a : Prop) : a ∨ true :=
begin
  refine_list,
end

open nat

example : ∀ n : ℕ, ∃ x : ℕ, x > n ∧ prime (x-1) ∧ prime (x+1) :=
begin
refine_list,
end

example : ∀ n : ℕ, ∃ p : ℕ, n*n < p ∧ p < (n+1)*(n+1) ∧ prime p :=
begin
refine_list,
end

example : ∀ n : ℕ, ∃ x : ℕ, x > n ∧ prime (x*x + 1) :=
begin
refine_list,
end
