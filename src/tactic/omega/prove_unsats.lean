/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.find_ees
import tactic.omega.find_scalars
import tactic.omega.lin_comb

open tactic 

meta def prove_neg : int → tactic expr 
| (int.of_nat _) := failed
| -[1+ m] := return `(int.neg_succ_lt_zero %%`(m))

meta def prove_forall_mem_eq_zero : nat → tactic expr 
| 0     := return `(@list.forall_mem_nil int (λ x : int, x = 0))
| (m+1) :=
  do x ← prove_forall_mem_eq_zero m, 
     return `(@list.forall_mem_cons_of int (λ x : int, x = 0) 
       0 (@list.repeat int 0 %%`(m)) (@eq.refl int 0) %%x)

meta def prove_unsat_lin_comb (ks : list nat) (p : list term) : tactic expr :=  
let ⟨b,as⟩ := lin_comb p ks in 
do x1 ← prove_neg b,
   x2 ← prove_forall_mem_eq_zero as.length, 
   to_expr ``(unsat_lin_comb_of %%`(p) %%`(ks) %%x1 %%x2)

/- Given a (([],les) : clause), return the 
   expr of a term (t : clause.unsat ([],les)). -/
meta def prove_unsat_ef : clause → tactic expr 
| ((_::_), _) := failed  
| ([], les) := 
  do ks ← find_scalars les, 
     x ← prove_unsat_lin_comb ks les,
     return `(unsat_of_unsat_lin_comb %%`(ks) %%`(les) %%x)

/- Given a (c : clause), return the 
   expr of a term (t : clause.unsat c)  -/
meta def prove_unsat (c : clause) : tactic expr := 
do ee ← find_ees c, 
   x ← prove_unsat_ef (eq_elim ee c), 
   return `(unsat_of_unsat_eq_elim %%`(ee) %%`(c) %%x)

/- Given a (cs : list clause), return the 
   expr of a term (t : clauses.unsat cs)  -/
meta def prove_unsats : list clause → tactic expr 
| [] := return `(clauses.unsat_nil)
| (p::ps) := 
  do x ← prove_unsat p,
     xs ← prove_unsats ps,
     to_expr ``(clauses.unsat_cons %%`(p) %%`(ps) %%x %%xs)
