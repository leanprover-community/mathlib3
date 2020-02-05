/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging linear integer & natural
number arithmetic goals using the Omega test. -/

import tactic.omega.int.main
import tactic.omega.nat.main

namespace omega

open tactic

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

/-- Detects domain of a formula from its expr.
* Returns none, if domain can be either ℤ or ℕ
* Returns some tt, if domain is exclusively ℤ
* Returns some ff, if domain is exclusively ℕ
* Fails, if domain is neither ℤ nor ℕ -/
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
| x                          := failed

meta def goal_domain_aux (x : expr) : tactic bool :=
(omega.int.wff x >> return tt) <|> (omega.nat.wff x >> return ff)

/-- Use the current goal to determine.
    Return tt if the domain is ℤ, and return ff if it is ℕ -/
meta def goal_domain : tactic bool :=
do gx ← target,
   hxs ← local_context >>= monad.mapm infer_type,
   app_first goal_domain_aux (gx::hxs)

/-- Return tt if the domain is ℤ, and return ff if it is ℕ -/
meta def determine_domain (opt : list name) : tactic bool :=
if `int ∈ opt
then return tt
else if `nat ∈ opt
     then return ff
     else goal_domain

end omega

open lean.parser interactive omega

/-- Attempts to discharge goals in the quantifier-free fragment of
linear integer and natural number arithmetic using the Omega test.
Guesses the correct domain by looking at the goal and hypotheses,
and then reverts all relevant hypotheses and variables.
Use `omega manual` to disable automatic reverts, and `omega int` or
`omega nat` to specify the domain. -/
meta def tactic.interactive.omega (opt : parse (many ident)) : tactic unit :=
do is_int ← determine_domain opt,
   let is_manual : bool := if `manaul ∈ opt then tt else ff,
   if is_int
   then omega_int is_manual
   else omega_nat is_manual
