/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging linear integer & natural 
number arithmetic goals using the Omega test.
-/

import tactic.omega.int.main 
import tactic.omega.nat.main 

namespace omega

open tactic

meta def revert_cond (t : expr → tactic unit) (x : expr) : tactic unit :=
(t x >> revert x >> skip) <|> skip 

meta def revert_cond_all (t : expr → tactic unit) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip

meta def select_domain (t s : tactic (option bool)) : tactic (option bool) :=
do a ← t, b ← s,
   match a, b with 
   | a,         none      := return a
   | none,      b         := return b
   | (some tt), (some tt) := return (some tt)
   | (some ff), (some ff) := return (some ff)
   | _,         _         := failed
   end

meta def type_domain (x : expr) : tactic (option bool) :=
if x = `(int)
then return (some tt)
else if x = `(nat) 
     then return (some ff)
     else failed

/- 
Detects domain of a formula from its expr. 
- Returns none, if domain can be either ℤ or ℕ 
- Returns some tt, if domain is exclusively ℤ 
- Returns some ff, if domain is exclusively ℕ
- Fails, if domain is neither ℤ nor ℕ 
-/
meta def form_domain : expr → tactic (option bool)
| `(¬ %%px)      := form_domain px
| `(%%px ∨ %%qx) := select_domain (form_domain px) (form_domain qx)
| `(%%px ∧ %%qx) := select_domain (form_domain px) (form_domain qx)
| `(%%px ↔ %%qx) := select_domain (form_domain px) (form_domain qx)
| `(%%(expr.pi _ _ px qx)) := 
  monad.cond 
    (if expr.has_var px then return tt else is_prop px)
    (select_domain (form_domain px) (form_domain qx))
    (select_domain (type_domain px) (form_domain qx))
| `(@has_lt.lt %%dx %%h _ _) := type_domain dx
| `(@has_le.le %%dx %%h _ _) := type_domain dx
| `(@eq %%dx _ _)            := type_domain dx
| `(@ge %%dx %%h _ _)        := type_domain dx
| `(@gt %%dx %%h _ _)        := type_domain dx
| `(@ne %%dx _ _)            := type_domain dx
| `(true)                    := return none 
| `(false)                   := return none 
| _                          := failed 

meta def term_domain (x : expr) : tactic (option bool) :=
infer_type x >>= type_domain

meta def is_lia_form (x : expr) : tactic unit :=
do (some tt) ← infer_type x >>= form_domain, skip

meta def is_lia_term (x : expr) : tactic unit :=
do (some tt) ← term_domain x, skip

meta def rev_lia : tactic unit :=
do revert_cond_all is_lia_form,
   revert_cond_all is_lia_term
   
meta def is_lna_form (x : expr) : tactic unit :=
do (some ff) ← infer_type x >>= form_domain, skip

meta def is_lna_term (x : expr) : tactic unit :=
do (some ff) ← term_domain x, skip

meta def rev_lna : tactic unit :=
do revert_cond_all is_lna_form,
   revert_cond_all is_lna_term
   
meta def goal_domain_aux : list expr → tactic bool 
| []      := failed
| (x::xs) := 
  do b1 ← ((form_domain x >>= return ∘ some) <|> return none),
     match b1 with 
     | none             := goal_domain_aux xs 
     | (some none)      := goal_domain_aux xs
     | (some (some tt)) := return tt
     | (some (some ff)) := return ff
     end

meta def goal_domain : tactic bool :=
do gx ← target,
   hxs ← local_context >>= monad.mapm infer_type,
   goal_domain_aux (gx::hxs)

meta def preprocess (opt : list name) : tactic unit :=
if `manual ∈ opt 
then skip
else if `int ∈ opt 
     then rev_lia
     else if `nat ∈ opt 
          then rev_lna
          else monad.cond goal_domain rev_lia rev_lna

end omega

open lean.parser interactive omega

meta def tactic.interactive.omega (opt : parse (many ident)) : tactic unit := 
preprocess opt >> 
if `int ∈ opt 
then omega_int
else if `nat ∈ opt 
     then omega_nat
     else monad.cond goal_domain omega_int omega_nat