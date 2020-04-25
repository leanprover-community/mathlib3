/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.mllist

@[reducible] def S (α : Type) := state_t (list nat) option α
def append (x : nat) : S unit :=
{ run := λ s, some ((), x :: s) }

def F : nat → S nat
| 0 := failure
| (n+1) := append (n+1) >> pure n

open tactic

run_cmd
(do let x := ((mllist.fix F 10).force).run [],
    guard $ x = (some ([10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])))
run_cmd
(do let x := (((mllist.fix F 10).map(λ n, n*n)).take 2).run [],
    guard $ x = (some ([100, 81], [9, 10])))
run_cmd
(do let x := (((mllist.fix F 10).mmap(λ n, pure $ n*n)).take 3).run [],
    guard $ x = (some ([100, 81, 64], [8, 9, 10])))

meta def l1 : mllist S nat := mllist.of_list [0,1,2]
meta def l2 : mllist S nat := mllist.of_list [3,4,5]
meta def ll : mllist S nat := (mllist.of_list [l1, l2]).join

run_cmd
(do let x := ll.force.run [],
    guard $ x = (some ([0, 1, 2, 3, 4, 5], [])))

meta def half_or_fail (n : ℕ) : tactic ℕ :=
do guard (n % 2 = 0),
   pure (n / 2)

run_cmd
(do let x : mllist tactic ℕ := mllist.range,
    let y := x.mfilter_map half_or_fail,
    z ← y.take 10,
    guard $ z.length = 10)

run_cmd
(do let R : mllist tactic ℕ := mllist.range,
    let S := R.mfilter_map (λ n, do guard $ n = 5, return n),
    n ← R.head,
    guard $ n = 0)

run_cmd
(do let R : mllist tactic ℕ := mllist.range,
    n ← R.mfirst (λ n, do guard $ n = 5, return n),
    guard $ n = 5)
