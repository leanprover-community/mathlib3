/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Main procedure for linear integer arithmetic. -/

import tactic.omega.prove_unsats
import tactic.omega.int.dnf
import tactic.omega.misc

open tactic

namespace omega
namespace int

open_locale omega.int

run_cmd mk_simp_attr `sugar
attribute [sugar]
  ne not_le not_lt
  int.lt_iff_add_one_le
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul
  one_mul mul_one
  mul_comm sub_eq_add_neg
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not

meta def desugar := `[try {simp only with sugar}]

lemma univ_close_of_unsat_clausify (m : nat) (p : preform) :
  clauses.unsat (dnf (¬* p)) → univ_close p (λ x, 0) m | h1 :=
begin
  apply univ_close_of_valid,
  apply valid_of_unsat_not,
  apply unsat_of_clauses_unsat,
  exact h1
end

/-- Given a (p : preform), return the expr of a (t : univ_close m p) -/
meta def prove_univ_close (m : nat) (p : preform) : tactic expr :=
do x ← prove_unsats (dnf (¬*p)),
   return `(univ_close_of_unsat_clausify %%`(m) %%`(p) %%x)

/-- Reification to imtermediate shadow syntax that retains exprs -/
meta def to_exprterm : expr → tactic exprterm
| `(- %%x) := --return (exprterm.exp (-1 : int) x)
  ( do z ← eval_expr' int x,
       return (exprterm.cst (-z : int)) ) <|>
  ( return $ exprterm.exp (-1 : int) x )
| `(%%mx * %%zx) :=
  do z ← eval_expr' int zx,
     return (exprterm.exp z mx)
| `(%%t1x + %%t2x) :=
  do t1 ← to_exprterm t1x,
     t2 ← to_exprterm t2x,
     return (exprterm.add t1 t2)
| x :=
  ( do z ← eval_expr' int x,
       return (exprterm.cst z) ) <|>
  ( return $ exprterm.exp 1 x )

/-- Reification to imtermediate shadow syntax that retains exprs -/
meta def to_exprform : expr → tactic exprform
| `(%%tx1 = %%tx2) :=
  do t1 ← to_exprterm tx1,
     t2 ← to_exprterm tx2,
     return (exprform.eq t1 t2)
| `(%%tx1 ≤ %%tx2) :=
  do t1 ← to_exprterm tx1,
     t2 ← to_exprterm tx2,
     return (exprform.le t1 t2)
| `(¬ %%px) := do p ← to_exprform px, return (exprform.not p)
| `(%%px ∨ %%qx) :=
  do p ← to_exprform px,
     q ← to_exprform qx,
     return (exprform.or p q)
| `(%%px ∧ %%qx) :=
  do p ← to_exprform px,
     q ← to_exprform qx,
     return (exprform.and p q)

| `(_ → %%px) := to_exprform px
| x := trace "Cannot reify expr : " >> trace x >> failed

/-- List of all unreified exprs -/
meta def exprterm.exprs : exprterm → list expr
| (exprterm.cst _)   := []
| (exprterm.exp _ x) := [x]
| (exprterm.add t s) := list.union t.exprs s.exprs

/-- List of all unreified exprs -/
meta def exprform.exprs : exprform → list expr
| (exprform.eq t s)  := list.union t.exprs s.exprs
| (exprform.le t s)  := list.union t.exprs s.exprs
| (exprform.not p)   := p.exprs
| (exprform.or p q)  := list.union p.exprs q.exprs
| (exprform.and p q) := list.union p.exprs q.exprs

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
meta def exprterm.to_preterm (xs : list expr) : exprterm → tactic preterm
| (exprterm.cst k)   := return & k
| (exprterm.exp k x) :=
  let m := xs.index_of x in
  if m < xs.length
  then return (k ** m)
  else failed
| (exprterm.add xa xb) :=
  do a ← xa.to_preterm,
     b ← xb.to_preterm,
     return (a +* b)

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
meta def exprform.to_preform (xs : list expr) : exprform → tactic preform
| (exprform.eq xa xb)  :=
   do a ← xa.to_preterm xs,
      b ← xb.to_preterm xs,
      return (a =* b)
| (exprform.le xa xb)  :=
   do a ← xa.to_preterm xs,
      b ← xb.to_preterm xs,
      return (a ≤* b)
| (exprform.not xp)    :=
  do p ← xp.to_preform,
     return ¬* p
| (exprform.or xp xq)  :=
  do p ← xp.to_preform,
     q ← xq.to_preform,
     return (p ∨* q)
| (exprform.and xp xq) :=
  do p ← xp.to_preform,
     q ← xq.to_preform,
     return (p ∧* q)

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms. -/
meta def to_preform (x : expr) : tactic (preform × nat) :=
do xf ← to_exprform x,
   let xs := xf.exprs,
   f ← xf.to_preform xs,
   return (f, xs.length)

/-- Return expr of proof of current LIA goal -/
meta def prove : tactic expr :=
do (p,m) ← target >>= to_preform,
   prove_univ_close m p

/-- Succeed iff argument is the expr of ℤ -/
meta def eq_int (x : expr) : tactic unit :=
if x = `(int) then skip else failed

/-- Check whether argument is expr of a well-formed formula of LIA-/
meta def wff : expr → tactic unit
| `(¬ %%px)      := wff px
| `(%%px ∨ %%qx) := wff px >> wff qx
| `(%%px ∧ %%qx) := wff px >> wff qx
| `(%%px ↔ %%qx) := wff px >> wff qx
| `(%%(expr.pi _ _ px qx)) :=
  monad.cond
     (if expr.has_var px then return tt else is_prop px)
     (wff px >> wff qx)
     (eq_int px >> wff qx)
| `(@has_lt.lt %%dx %%h _ _) := eq_int dx
| `(@has_le.le %%dx %%h _ _) := eq_int dx
| `(@eq %%dx _ _)            := eq_int dx
| `(@ge %%dx %%h _ _)        := eq_int dx
| `(@gt %%dx %%h _ _)        := eq_int dx
| `(@ne %%dx _ _)            := eq_int dx
| `(true)                    := skip
| `(false)                   := skip
| _                          := failed

/-- Succeed iff argument is expr of term whose type is wff -/
meta def wfx (x : expr) : tactic unit :=
infer_type x >>= wff

/-- Intro all universal quantifiers over ℤ -/
meta def intro_ints_core : tactic unit :=
do x ← target,
   match x with
   | (expr.pi _ _ `(int) _) := intro_fresh >> intro_ints_core
   | _                      := skip
   end

meta def intro_ints : tactic unit :=
do (expr.pi _ _ `(int) _) ← target,
   intro_ints_core

/-- If the goal has universal quantifiers over integers, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear integer arithmetic. -/
meta def preprocess : tactic unit :=
intro_ints <|> (revert_cond_all wfx >> desugar)

end int
end omega

open omega.int

/-- The core omega tactic for integers. -/
meta def omega_int (is_manual : bool) : tactic unit :=
desugar ; (if is_manual then skip else preprocess) ; prove >>= apply >> skip
