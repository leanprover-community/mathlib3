/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
Main procedure for linear natural number arithmetic.
-/

import tactic.omega.prove_unsats
import tactic.omega.nat.dnf
import tactic.omega.nat.neg_elim
import tactic.omega.nat.sub_elim

open tactic

namespace omega
namespace nat

open_locale omega.nat

run_cmd mk_simp_attr `sugar_nat

attribute [sugar_nat]
  ne not_le not_lt
  nat.lt_iff_add_one_le
  nat.succ_eq_add_one
  or_false false_or
  and_true true_and
  ge gt mul_add add_mul mul_comm
  one_mul mul_one
  imp_iff_not_or
  iff_iff_not_or_and_or_not

meta def desugar := `[try {simp only with sugar_nat at *}]

lemma univ_close_of_unsat_neg_elim_not (m) (p : preform) :
  (neg_elim (¬* p)).unsat → univ_close p (λ _, 0) m :=
begin
  intro h1, apply univ_close_of_valid,
  apply valid_of_unsat_not, intro h2, apply h1,
  apply preform.sat_of_implies_of_sat implies_neg_elim h2,
end

/-- Return expr of proof that argument is free of subtractions -/
meta def preterm.prove_sub_free : preterm → tactic expr
| (& m)    := return `(trivial)
| (m ** n) := return `(trivial)
| (t +* s) :=
  do x ← preterm.prove_sub_free t,
     y ← preterm.prove_sub_free s,
     return `(@and.intro (preterm.sub_free %%`(t))
       (preterm.sub_free %%`(s)) %%x %%y)
| (_ -* _) := failed

/-- Return expr of proof that argument is free of negations -/
meta def prove_neg_free : preform → tactic expr
| (t =* s) := return `(trivial)
| (t ≤* s) := return `(trivial)
| (p ∨* q) :=
  do x ← prove_neg_free p,
     y ← prove_neg_free q,
     return `(@and.intro (preform.neg_free %%`(p))
       (preform.neg_free %%`(q)) %%x %%y)
| (p ∧* q) :=
  do x ← prove_neg_free p,
     y ← prove_neg_free q,
     return `(@and.intro (preform.neg_free %%`(p))
       (preform.neg_free %%`(q)) %%x %%y)
| _        := failed

/-- Return expr of proof that argument is free of subtractions -/
meta def prove_sub_free : preform → tactic expr
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
     return `(@and.intro (preform.sub_free %%`(p))
       (preform.sub_free %%`(q)) %%x %%y)
| (p ∧* q) :=
  do x ← prove_sub_free p,
     y ← prove_sub_free q,
     return `(@and.intro (preform.sub_free %%`(p))
       (preform.sub_free %%`(q)) %%x %%y)

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is subtraction- and
negation-free. -/
meta def prove_unsat_sub_free (p : preform) : tactic expr :=
do x ← prove_neg_free p,
   y ← prove_sub_free p,
   z ← prove_unsats (dnf p),
   return `(unsat_of_unsat_dnf %%`(p) %%x %%y %%z)

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is negation-free. -/
meta def prove_unsat_neg_free : preform → tactic expr | p :=
match p.sub_terms with
| none         := prove_unsat_sub_free p
| (some (t,s)) :=
  do x ← prove_unsat_neg_free (sub_elim t s p),
     return `(unsat_of_unsat_sub_elim %%`(t) %%`(s) %%`(p) %%x)
end

/-- Given a (m : nat) and (p : preform), return the expr of (t : univ_close m p). -/
meta def prove_univ_close (m : nat) (p : preform) : tactic expr :=
do x ← prove_unsat_neg_free (neg_elim (¬*p)),
   to_expr ``(univ_close_of_unsat_neg_elim_not %%`(m) %%`(p) %%x)

/-- Reification to imtermediate shadow syntax that retains exprs -/
meta def to_exprterm : expr → tactic exprterm
| `(%%x * %%y) :=
  do m ← eval_expr' nat y,
     return (exprterm.exp m x)
| `(%%t1x + %%t2x) :=
  do t1 ← to_exprterm t1x,
     t2 ← to_exprterm t2x,
     return (exprterm.add t1 t2)
| `(%%t1x - %%t2x) :=
  do t1 ← to_exprterm t1x,
     t2 ← to_exprterm t2x,
     return (exprterm.sub t1 t2)
| x :=
  ( do m ← eval_expr' nat x,
       return (exprterm.cst m) ) <|>
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
| (exprterm.sub t s) := list.union t.exprs s.exprs

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
| (exprterm.sub xa xb) :=
  do a ← xa.to_preterm,
     b ← xb.to_preterm,
     return (a -* b)

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

/-- Return expr of proof of current LNA goal -/
meta def prove : tactic expr :=
do (p,m) ← target >>= to_preform,
   trace_if_enabled `omega p,
   prove_univ_close m p

/-- Succeed iff argument is expr of ℕ -/
meta def eq_nat (x : expr) : tactic unit :=
if x = `(nat) then skip else failed

/-- Check whether argument is expr of a well-formed formula of LNA-/
meta def wff : expr → tactic unit
| `(¬ %%px)      := wff px
| `(%%px ∨ %%qx) := wff px >> wff qx
| `(%%px ∧ %%qx) := wff px >> wff qx
| `(%%px ↔ %%qx) := wff px >> wff qx
| `(%%(expr.pi _ _ px qx)) :=
  monad.cond
     (if expr.has_var px then return tt else is_prop px)
     (wff px >> wff qx)
     (eq_nat px >> wff qx)
| `(@has_lt.lt %%dx %%h _ _) := eq_nat dx
| `(@has_le.le %%dx %%h _ _) := eq_nat dx
| `(@eq %%dx _ _)            := eq_nat dx
| `(@ge %%dx %%h _ _)        := eq_nat dx
| `(@gt %%dx %%h _ _)        := eq_nat dx
| `(@ne %%dx _ _)            := eq_nat dx
| `(true)                    := skip
| `(false)                   := skip
| _                          := failed

/-- Succeed iff argument is expr of term whose type is wff -/
meta def wfx (x : expr) : tactic unit :=
infer_type x >>= wff

/-- Intro all universal quantifiers over nat -/
meta def intro_nats_core : tactic unit :=
do x ← target,
   match x with
   | (expr.pi _ _ `(nat) _) := intro_fresh >> intro_nats_core
   | _                      := skip
   end

meta def intro_nats : tactic unit :=
do (expr.pi _ _ `(nat) _) ← target,
   intro_nats_core

/-- If the goal has universal quantifiers over natural, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear natural number arithmetic. -/
meta def preprocess : tactic unit :=
intro_nats <|> (revert_cond_all wfx >> desugar)

end nat
end omega

open omega.nat

/-- The core omega tactic for natural numbers. -/
meta def omega_nat (is_manual : bool) : tactic unit :=
desugar ; (if is_manual then skip else preprocess) ; prove >>= apply >> skip
