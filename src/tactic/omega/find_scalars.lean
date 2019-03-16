/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.term

meta def trisect (m : nat) :  
  list (list nat × term) → (list (list nat × term) × 
  list (list nat × term) × list (list nat × term)) 
| [] := ([],[],[])
| ((p,t)::pts) := 
  let (neg,zero,pos) := trisect pts in 
  if t.snd.get m < 0 
  then ((p,t)::neg,zero,pos)
  else if t.snd.get m = 0 
       then (neg,(p,t)::zero,pos)
       else (neg,zero,(p,t)::pos)

meta def elim_var_aux (m : nat) : 
  ((list nat × term) × (list nat × term)) → tactic (list nat × term) 
| ((p1,t1), (p2,t2)) := 
  let n := int.nat_abs (t1.snd.get m) in
  let o := int.nat_abs (t2.snd.get m) in
  let lcm := (nat.lcm n o) in
  let n' := lcm / n in
  let o' := lcm / o in
  return (list.add (p1.map ((*) n')) (p2.map ((*) o')), 
          term.add (t1.mul n') (t2.mul o'))

meta def elim_var (m) (neg pos : list (list nat × term)) : 
  tactic (list (list nat × term)) :=
let pairs := list.product neg pos in 
monad.mapm (elim_var_aux m) pairs

meta def find_neg_const : list (list nat × term) → tactic (list nat)
| []            := tactic.failed
| ((π,⟨c,_⟩)::l) := if c < 0 then return π else find_neg_const l

meta def find_scalars_core : nat → list (list nat × term) → tactic (list nat) 
| 0 pts     := find_neg_const pts
| (m+1) pts :=
  let (neg,zero,pos) := trisect m pts in
  do new ← elim_var m neg pos,
     find_scalars_core m (new ++ zero)

meta def find_scalars (ts : list term) : tactic (list nat) :=
find_scalars_core 
  (ts.map (λ t : term, t.snd.length)).max  
  (ts.map_with_index (λ m t, ([]{m ↦ 1}, t)))
