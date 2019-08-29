/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire

example (p q : nat) :
   (forall x y z : nat, x * (y * z) = (x * y) * z) ∧ p * q * p = p
   → exists q' : nat, p * q' * p = p ∧ q' * p * q' = q' := by vampire

#exit
instance int.inhabited : inhabited int := ⟨0⟩ 

example (i : int → int) (e : int) :
   (forall x y z : int, x * (y * z) = (x * y) * z) ∧
   (forall x : int, e * x = x) ∧
   (forall x : int, i x * x = e) → 
   forall x : int, x * e = x := by vampire
#exit

example (i : nat → nat) (e : nat) :
   (forall x y z : nat, x * (y * z) = (x * y) * z) ∧
   (forall x : nat, e * x = x) ∧
   (forall x : nat, i x * x = e) →
   forall x : nat, x * i x = e :=
by vampire

example :
   (exists x, x = f(g(x)) ∧ forall x', x' = f(g(x')) → x = x') ↔
   (exists y, y = g(f(y)) ∧ forall y', y' = g(f(y')) → y = y') :=
by vampire


let group2 =
   (forall x y z. x * (y * z) = (x * y) * z) ∧
   (forall x, e * x = x) ∧
   (forall x, i(x) * x = e)
   → forall x, x * i(x) = e := sorry

