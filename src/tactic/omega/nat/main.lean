/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Main procedure for linear natural number arithmetic.
-/

import tactic.omega.prove_unsats
import tactic.omega.nat.dnf
import tactic.omega.nat.neg_elim

open tactic 

namespace omega
namespace nat

local notation `&` k    := preterm.cst k
local infix `**`  : 300 := preterm.var 
local notation t `+*` s := preterm.add t s
local notation t `-*` s := preterm.sub t s

local notation x `=*` y := form.eq x y
local notation x `≤*` y := form.le x y
local notation `¬*` p   := form.not p
local notation p `∨*` q := form.or p q
local notation p `∧*` q := form.and p q

   
run_cmd mk_simp_attr `sugar_nat 
attribute [sugar_nat] 
  not_le not_lt
  nat.lt_iff_add_one_le
  nat.succ_eq_add_one
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul mul_comm
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not

meta def desugar := `[try {simp only with sugar_nat}]

lemma univ_close_of_unsat_neg_elim_not (m) (p : form) :
  (neg_elim (¬* p)).unsat → univ_close p (λ _, 0) m :=  
begin
  intro h1, apply univ_close_of_valid,
  apply valid_of_unsat_not, intro h2, apply h1,
  apply form.sat_of_implies_of_sat implies_neg_elim h2,
end

meta def preterm.prove_sub_free : preterm → tactic expr 
| (& m)    := return `(trivial)
| (m ** n) := return `(trivial)
| (t +* s) := 
  do x ← preterm.prove_sub_free t,
     y ← preterm.prove_sub_free s,
     return `(@and.intro (preterm.sub_free %%`(t)) 
       (preterm.sub_free %%`(s)) %%x %%y) 
| (_ -* _) := failed

meta def prove_neg_free : form → tactic expr 
| (t =* s) := return `(trivial)
| (t ≤* s) := return `(trivial)
| (p ∨* q) := 
  do x ← prove_neg_free p,
     y ← prove_neg_free q,
     return `(@and.intro (form.neg_free %%`(p)) 
       (form.neg_free %%`(q)) %%x %%y) 
| (p ∧* q) := 
  do x ← prove_neg_free p,
     y ← prove_neg_free q,
     return `(@and.intro (form.neg_free %%`(p)) 
       (form.neg_free %%`(q)) %%x %%y) 
| _        := failed

meta def prove_sub_free : form → tactic expr 
| (t =* s) := 
  do x ← preterm.prove_sub_free t,
     y ← preterm.prove_sub_free s,
     return `(@and.intro (preterm.sub_free %%`(t)) 
       (preterm.sub_free %%`(s)) %%x %%y) 
| (t ≤* s) := 
  do x ← preterm.prove_sub_free t,
     y ← preterm.prove_sub_free s,
     return `(@and.intro (preterm.sub_free %%`(t)) 
       (preterm.sub_free %%`(s)) %%x %%y) 
| (¬*p) := prove_sub_free p
| (p ∨* q) := 
  do x ← prove_sub_free p,
     y ← prove_sub_free q,
     return `(@and.intro (form.sub_free %%`(p)) 
       (form.sub_free %%`(q)) %%x %%y) 
| (p ∧* q) := 
  do x ← prove_sub_free p,
     y ← prove_sub_free q,
     return `(@and.intro (form.sub_free %%`(p)) 
       (form.sub_free %%`(q)) %%x %%y) 

/- Given a p : form, return the expr of a term t : p.unsat,
   where p is subtraction- and negation-free. -/
meta def prove_unsat_sub_free (p : form) : tactic expr :=  
do x ← prove_neg_free p,
   y ← prove_sub_free p,
   z ← prove_unsats (dnf p),
   return `(unsat_of_unsat_dnf %%`(p) %%x %%y %%z)

/- Given a p : form, return the expr of a term t : p.unsat,
   where p is negation-free. -/
meta def prove_unsat_neg_free : form → tactic expr | p := 
match p.sub_terms with 
| none         := prove_unsat_sub_free p
| (some (t,s)) := 
  do x ← prove_unsat_neg_free (sub_elim t s p), 
     return `(unsat_of_unsat_sub_elim %%`(t) %%`(s) %%`(p) %%x)
end

/- Given a (m : nat) and (p : form), 
   return the expr of (t : univ_close m p) -/
meta def prove_univ_close (m : nat) (p : form) : tactic expr := 
do x ← prove_unsat_neg_free (neg_elim (¬*p)), 
   to_expr ``(univ_close_of_unsat_neg_elim_not %%`(m) %%`(p) %%x)

meta def to_preterm : expr → tactic preterm 
| (expr.var k) := return (preterm.var 1 k)
| `(%%(expr.var k) * %%mx) := 
  do m ← eval_expr nat mx, 
     return (preterm.var m k)
| `(%%t1x + %%t2x) := 
  do t1 ← to_preterm t1x, 
     t2 ← to_preterm t2x, 
     return (preterm.add t1 t2)
| `(%%t1x - %%t2x) := 
  do t1 ← to_preterm t1x, 
     t2 ← to_preterm t2x, 
     return (preterm.sub t1 t2)
| mx := 
  do m ← eval_expr nat mx,
     return (preterm.cst m)

meta def to_form_core : expr → tactic form 
| `(%%tx1 = %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 =* t2)
| `(%%tx1 ≤ %%tx2) := 
  do t1 ← to_preterm tx1, 
     t2 ← to_preterm tx2, 
     return (t1 ≤* t2)
| `(¬ %%px) := do p ← to_form_core px, return (¬* p)
| `(%%px ∨ %%qx) := 
  do p ← to_form_core px, 
     q ← to_form_core qx, 
     return (p ∨* q)
| `(%%px ∧ %%qx) := 
  do p ← to_form_core px, 
     q ← to_form_core qx, 
     return (p ∧* q)
| `(_ → %%px) := to_form_core px
| _ := failed

meta def to_form : nat → expr → tactic (form × nat) 
| m `(_ → %%px) := to_form (m+1) px
| m x := do p ← to_form_core x, return (p,m)

meta def prove_lna : tactic expr :=
do (p,m) ← target >>= to_form 0,
   prove_univ_close m p 

end nat
end omega

open omega.nat

meta def omega_nat : tactic unit :=
desugar >> prove_lna >>= apply >> skip