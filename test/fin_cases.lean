/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.nat.interval
import data.nat.prime
import group_theory.perm.sign
import tactic.fin_cases

example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *,
  simp, assumption,
  simp, assumption,
  simp, assumption,
end

example (f : ℕ → Prop) (p : fin 0) : f p.val :=
by fin_cases *

example (f : ℕ → Prop) (p : fin 1) (h : f 0) : f p.val :=
begin
  fin_cases p,
  assumption
end

example (x2 : fin 2) (x3 : fin 3) (n : nat) (y : fin n) : x2.val * x3.val = x3.val * x2.val :=
begin
  fin_cases x2;
  fin_cases x3,
  success_if_fail { fin_cases * },
  success_if_fail { fin_cases y },
  all_goals { refl },
end

open finset
example (x : ℕ) (h : x ∈ Ico 2 5) : x = 2 ∨ x = 3 ∨ x = 4 :=
begin
  fin_cases h,
  all_goals { simp }
end

open nat
example (x : ℕ) (h : x ∈ [2,3,5,7]) : x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 7 :=
begin
  fin_cases h,
  all_goals { simp }
end

example (x : ℕ) (h : x ∈ [2,3,5,7]) : true :=
begin
  success_if_fail { fin_cases h with [3,3,5,7] },
  trivial
end

example (x : list ℕ) (h : x ∈ [[1],[2]]) : x.length = 1 :=
begin
  fin_cases h with [[1],[1+1]],
  simp,
  guard_target (list.length [1 + 1] = 1),
  simp
end

 -- testing that `with` arguments are elaborated with respect to the expected type:
example (x : ℤ) (h : x ∈ ([2,3] : list ℤ)) : x = 2 ∨ x = 3 :=
begin
  fin_cases h with [2,3],
  all_goals { simp }
end


instance (n : ℕ) : decidable (nat.prime n) := decidable_prime_1 n
example (x : ℕ) (h : x ∈ (range 10).filter nat.prime) : x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 7 :=
begin
  fin_cases h; exact dec_trivial
end

open equiv.perm
example (x : (Σ (a : fin 4), fin 4)) (h : x ∈ fin_pairs_lt 4) : x.1.val < 4 :=
begin
  fin_cases h; simp,
  any_goals { exact dec_trivial },
end

example (x : fin 3) : x.val < 5 :=
begin
  fin_cases x; exact dec_trivial
end

example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *,
  all_goals { assumption }
end

example (n : ℕ) (h : n % 3 ∈ [0,1]) : true :=
begin
  fin_cases h,
  guard_hyp h : n % 3 = 0, trivial,
  guard_hyp h : n % 3 = 1, trivial,
end

/-
In some circumstances involving `let`,
the temporary hypothesis that `fin_cases` creates does not get deleted.
We test that this is correctly named and that the name can be changed.

Note: after `fin_cases`, we have `this : (a : fin 3) = (0 : fin (2 + 1))`
for some reason. I don't know why, and it complicates the test.
-/
example (f : ℕ → fin 3) : true :=
begin
  let a := f 3,
  fin_cases a,
  guard_hyp a := f 3,
  guard_hyp this : a = (0 : fin (2 + 1)),
  trivial, trivial,

  let b := f 2,
  fin_cases b using what,
  guard_hyp what : b = (0 : fin (2 + 1)),

  all_goals {trivial}
end

/-
The behavior above can be worked around with `fin_cases with`.
-/
example (f : ℕ → fin 3) : true :=
begin
  let a := f 3,
  fin_cases a with [0, 1, 2],
  guard_hyp a := f 3,
  guard_hyp this : a = 0,
  trivial,
  guard_hyp this : a = 1,
  trivial,
  guard_hyp this : a = 2,
  let b := f 2,
  fin_cases b with [0, 1, 2] using what,
  guard_hyp what : b = 0,
  all_goals {trivial}
end
