/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.int.main 
import tactic.omega.nat.main 

open tactic

meta def is_hyp (x : expr) : tactic bool :=
infer_type x >>= is_prop

meta def is_int (x : expr) : tactic bool :=
if x = `(int) then return tt
else if x = `(nat) then return ff
     else failed

meta def is_lia_form : expr → tactic bool
| `(¬ %%px)      := is_lia_form px
| `(%%px ∨ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%px ∧ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%px ↔ %%qx) := is_lia_form px <|> is_lia_form qx
| `(%%(expr.pi _ _ px qx)) := 
  (monad.cond 
    (if expr.has_var px then return tt else is_prop px)
    (is_lia_form px) (is_int px)) <|> 
  (is_lia_form qx)
| `(@has_lt.lt %%dx %%h _ _) := is_int dx
| `(@has_le.le %%dx %%h _ _) := is_int dx
| `(@eq %%dx _ _) := is_int dx
| `(@ge %%dx %%h _ _) := is_int dx
| `(@gt %%dx %%h _ _) := is_int dx
| `(@ne %%dx _ _) := is_int dx
| _ := failed 
  
meta def is_lia_goal_aux : list expr → tactic bool 
| []      := failed
| (x::xs) := is_lia_form x <|> is_lia_goal_aux xs

meta def is_lia_goal : tactic bool :=
do gx ← target,
   hxs ← local_context >>= monad.mapm infer_type,
   is_lia_goal_aux (gx::hxs)
   
meta def omega (is_lia : option bool := none) : tactic unit := 
match is_lia with 
| some tt := int.omega
| some ff := nat.omega
| none    := monad.cond is_lia_goal int.omega nat.omega 
end