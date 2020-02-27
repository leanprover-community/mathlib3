/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging linear integer & natural
number arithmetic goals using the Omega test.
-/

import tactic.omega.int.main
import tactic.omega.nat.main
import tactic.doc_commands

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
| x                          := failed

meta def form_wf (x : expr) : tactic bool :=
(form_domain x >> return tt) <|> return ff

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

meta def clear_unused_hyp (hx : expr) : tactic unit :=
do x ← infer_type hx,
   b ← form_wf x,
   if (b ∨ x = `(nat) ∨ x = `(int))
   then skip
   else clear hx >> skip

meta def clear_unused_hyps : tactic unit :=
local_context >>= mmap' clear_unused_hyp

meta def preprocess (opt : list name) : tactic unit :=
if `manual ∈ opt
then skip
else clear_unused_hyps >>
     if `int ∈ opt
     then rev_lia
     else if `nat ∈ opt
          then rev_lna
          else monad.cond goal_domain rev_lia rev_lna

end omega

open lean.parser interactive omega

/--
Attempts to discharge goals in the quantifier-free fragment of
linear integer and natural number arithmetic using the Omega test.
Guesses the correct domain by looking at the goal and hypotheses,
and then reverts all relevant hypotheses and variables.
Use `omega manual` to disable automatic reverts, and `omega int` or
`omega nat` to specify the domain.

---

`omega` attempts to discharge goals in the quantifier-free fragment of linear integer and natural number arithmetic using the Omega test. In other words, the core procedure of `omega` works with goals of the form
```lean
∀ x₁, ... ∀ xₖ, P
```
where `x₁, ... xₖ` are integer (resp. natural number) variables, and `P` is a quantifier-free formula of linear integer (resp. natural number) arithmetic. For instance:
```lean
example : ∀ (x y : int), (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega
```
By default, `omega` tries to guess the correct domain by looking at the goal and hypotheses, and then reverts all relevant hypotheses and variables (e.g., all variables of type `nat` and `Prop`s in linear natural number arithmetic, if the domain was determined to be `nat`) to universally close the goal before calling the main procedure. Therefore, `omega` will often work even if the goal is not in the above form:
```lean
example (x y : nat) (h : 2 * x + 1 = 2 * y) : false := by omega
```
But this behaviour is not always optimal, since it may revert irrelevant hypotheses or incorrectly guess the domain. Use `omega manual` to disable automatic reverts, and `omega int` or `omega nat` to specify the domain.
```lean
example (x y z w : int) (h1 : 3 * y ≥ x) (h2 : z > 19 * w) : 3 * x ≤ 9 * y :=
by {revert h1 x y, omega manual}

example (i : int) (n : nat) (h1 : i = 0) (h2 : n < n) : false := by omega nat

example (n : nat) (h1 : n < 34) (i : int) (h2 : i * 9 = -72) : i = -8 :=
by {revert h2 i, omega manual int}
```
`omega` handles `nat` subtraction by repeatedly rewriting goals of the form `P[t-s]` into `P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh. This means that each (distinct) occurrence of subtraction will cause the goal size to double during DNF transformation.

`omega` implements the real shadow step of the Omega test, but not the dark and gray shadows. Therefore, it should (in principle) succeed whenever the negation of the goal has no real solution, but it may fail if a real solution exists, even if there is no integer/natural number solution.
-/
meta def tactic.interactive.omega (opt : parse (many ident)) : tactic unit :=
preprocess opt >>
if `int ∈ opt
then omega_int
else if `nat ∈ opt
     then omega_nat
     else mcond goal_domain omega_int omega_nat

add_hint_tactic "omega"

add_tactic_doc
{ name       := "omega",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.omega],
  tags       := ["simplification", "normalization", "arithmetic", "decision procedure"] }
