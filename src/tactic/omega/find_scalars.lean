/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
Tactic for performing Fourier–Motzkin elimination to find
a contradictory linear combination of input constraints.
-/

import tactic.omega.term
import data.list.min_max

open list.func

namespace omega

/-- Divide linear combinations into three groups by the coefficient of the
    `m`th variable in their resultant terms: negative, zero, or positive. -/
meta def trisect (m : nat) :
  list (list nat × term) → (list (list nat × term) ×
  list (list nat × term) × list (list nat × term))
| [] := ([],[],[])
| ((p,t)::pts) :=
  let (neg,zero,pos) := trisect pts in
  if get m t.snd < 0
  then ((p,t)::neg,zero,pos)
  else if get m t.snd = 0
       then (neg,(p,t)::zero,pos)
       else (neg,zero,(p,t)::pos)

/-- Use two linear combinations to obtain a third linear combination
    whose resultant term does not include the `m`th variable. -/
meta def elim_var_aux (m : nat) :
  ((list nat × term) × (list nat × term)) → tactic (list nat × term)
| ((p1,t1), (p2,t2)) :=
  let n := int.nat_abs (get m t1.snd) in
  let o := int.nat_abs (get m t2.snd) in
  let lcm := (nat.lcm n o) in
  let n' := lcm / n in
  let o' := lcm / o in
  return (add (p1.map ((*) n')) (p2.map ((*) o')),
          term.add (t1.mul n') (t2.mul o'))

/-- Use two lists of linear combinations (one in which the resultant terms
    include occurrences of the `m`th variable with positive coefficients,
    and one with negative coefficients) and linearly combine them in every
    possible way that eliminates the `m`th variable. -/
meta def elim_var (m : nat) (neg pos : list (list nat × term)) :
  tactic (list (list nat × term)) :=
let pairs := list.product neg pos in
monad.mapm (elim_var_aux m) pairs

/-- Search through a list of (linear combination × resultant term) pairs,
    find the first pair whose resultant term has a negative constant term,
    and return its linear combination -/
meta def find_neg_const : list (list nat × term) → tactic (list nat)
| []            := tactic.failed
| ((π,⟨c,_⟩)::l) := if c < 0 then return π else find_neg_const l

/-- First, eliminate all variables by Fourier–Motzkin elimination.
    When all variables have been eliminated, find and return the
    linear combination which produces a constraint of the form
    `0 < k + t` such that `k` is the constant term of the RHS and `k < 0`. -/
meta def find_scalars_core : nat → list (list nat × term) → tactic (list nat)
| 0 pts     := find_neg_const pts
| (m+1) pts :=
  let (neg,zero,pos) := trisect m pts in
  do new ← elim_var m neg pos,
     find_scalars_core m (new ++ zero)

/-- Perform Fourier–Motzkin elimination to find a contradictory
    linear combination of input constraints. -/
meta def find_scalars (ts : list term) : tactic (list nat) :=
find_scalars_core
  (ts.map (λ t : term, t.snd.length)).maximum.iget
  (ts.map_with_index (λ m t, (list.func.set 1 [] m, t)))

end omega
