/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Main procedure for linear integer arithmetic.
-/

import tactic.omega.prove_unsats
import tactic.omega.int.dnf

open tactic

namespace omega
namespace int

local notation x ` =* ` y := form.eq x y
local notation x ` ≤* ` y := form.le x y
local notation `¬* ` p   := form.not p
local notation p ` ∨* ` q := form.or p q
local notation p ` ∧* ` q := form.and p q

run_cmd mk_simp_attr `sugar
attribute [sugar]
  not_le not_lt
  int.lt_iff_add_one_le
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul
  mul_comm sub_eq_add_neg
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not

meta def desugar := `[try {simp only with sugar}]

lemma univ_close_of_unsat_clausify (m : nat) (p : form) :
  clauses.unsat (dnf (¬* p)) → univ_close p (λ x, 0) m | h1 :=
begin
  apply univ_close_of_valid,
  apply valid_of_unsat_not,
  apply unsat_of_clauses_unsat,
  exact h1
end

/- Given a (p : form), return the expr of a (t : univ_close m p) -/
meta def prove_univ_close (m : nat) (p : form) : tactic expr :=
do x ← prove_unsats (dnf (¬*p)),
   return `(univ_close_of_unsat_clausify %%`(m) %%`(p) %%x)

meta def to_preterm : expr → tactic preterm
| (expr.var k) := return (preterm.var 1 k)
| `(-%%(expr.var k)) := return (preterm.var (-1 : int) k)
| `(%%(expr.var k) * %%zx) :=
  do z ← eval_expr int zx,
     return (preterm.var z k)
| `(%%t1x + %%t2x) :=
  do t1 ← to_preterm t1x,
     t2 ← to_preterm t2x,
     return (preterm.add t1 t2)
| zx :=
  do z ← eval_expr int zx,
     return (preterm.cst z)

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
| _ := failed

meta def to_form : nat → expr → tactic (form × nat)
| m `(_ → %%px) := to_form (m+1) px
| m x := do p ← to_form_core x, return (p,m)

meta def prove_lia : tactic expr :=
do (p,m) ← target >>= to_form 0,
   prove_univ_close m p

end int
end omega

open omega.int

meta def omega_int : tactic unit :=
desugar >> prove_lia >>= apply >> skip
