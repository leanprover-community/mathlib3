/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic which constructs exprs to discharge
goals of the form `clauses.unsat cs`. -/

import tactic.omega.find_ees
import tactic.omega.find_scalars
import tactic.omega.lin_comb

namespace omega

open tactic

/-- Return expr of proof that given int is negative -/
meta def prove_neg : int → tactic expr
| (int.of_nat _) := failed
| -[1+ m] := return `(int.neg_succ_lt_zero %%`(m))

lemma forall_mem_repeat_zero_eq_zero (m : nat) :
  (∀ x ∈ (list.repeat (0 : int) m), x = (0 : int)) :=
λ x, list.eq_of_mem_repeat

/-- Return expr of proof that elements of (repeat 0 is.length) are all 0 -/
meta def prove_forall_mem_eq_zero (is : list int) : tactic expr :=
return `(forall_mem_repeat_zero_eq_zero is.length)

/-- Return expr of proof that the combination of linear constraints
    represented by ks and ts is unsatisfiable -/
meta def prove_unsat_lin_comb (ks : list nat) (ts : list term) : tactic expr :=
let ⟨b,as⟩ := lin_comb ks ts in
do x1 ← prove_neg b,
   x2 ← prove_forall_mem_eq_zero as,
   to_expr ``(unsat_lin_comb_of %%`(ks) %%`(ts) %%x1 %%x2)

/-- Given a (([],les) : clause), return the expr of a term (t : clause.unsat ([],les)). -/
meta def prove_unsat_ef : clause → tactic expr
| ((_::_), _) := failed
| ([], les) :=
  do ks ← find_scalars les,
     x ← prove_unsat_lin_comb ks les,
     return `(unsat_of_unsat_lin_comb %%`(ks) %%`(les) %%x)

/-- Given a (c : clause), return the expr of a term (t : clause.unsat c)  -/
meta def prove_unsat (c : clause) : tactic expr :=
do ee ← find_ees c,
   x ← prove_unsat_ef (eq_elim ee c),
   return `(unsat_of_unsat_eq_elim %%`(ee) %%`(c) %%x)

/-- Given a (cs : list clause), return the expr of a term (t : clauses.unsat cs)  -/
meta def prove_unsats : list clause → tactic expr
| [] := return `(clauses.unsat_nil)
| (p::ps) :=
  do x ← prove_unsat p,
     xs ← prove_unsats ps,
     to_expr ``(clauses.unsat_cons %%`(p) %%`(ps) %%x %%xs)

end omega
