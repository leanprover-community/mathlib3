/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Linear integer arithmetic terms in pre-normalized form. -/

import tactic.split_ifs tactic.omega.term

namespace omega
namespace int

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `-5` is reified to `cst -5`) and all other atomic terms are reified to
`exp` (e.g., `-5 * (gcd 14 -7)` is reified to `exp -5 \`(gcd 14 -7)`).
`exp` accepts a coefficient of type `int` as its first argument because
multiplication by constant is allowed by the omega test. -/
meta inductive exprterm : Type
| cst : int → exprterm
| exp : int → expr → exprterm
| add : exprterm → exprterm → exprterm

/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
@[derive has_reflect]
inductive preterm : Type
| cst : int → preterm
| var : int → nat → preterm
| add : preterm → preterm → preterm

localized "notation `&` k    := omega.int.preterm.cst k" in omega.int
localized "infix ` ** ` : 300 := omega.int.preterm.var" in omega.int
localized "notation t `+*` s := omega.int.preterm.add t s" in omega.int

namespace preterm

/-- Preterm evaluation -/
@[simp] def val (v : nat → int) : preterm → int
| (& i) := i
| (i ** n) :=
  if i = 1
  then v n
  else if i = -1
       then -(v n)
       else (v n) * i
| (t1 +* t2) := t1.val + t2.val

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preterm → nat
| (& _) := 0
| (i ** n) := n + 1
| (t1 +* t2) := max t1.fresh_index t2.fresh_index

@[simp] def add_one (t : preterm) : preterm := t +* (&1)

def repr : preterm → string
| (& i) := i.repr
| (i ** n) := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"

end preterm

open_locale list.func -- get notation for list.func.set

/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp] def canonize : preterm → term
| (& i)      := ⟨i, []⟩
| (i ** n)   := ⟨0, [] {n ↦ i}⟩
| (t1 +* t2) := term.add (canonize t1) (canonize t2)

@[simp] lemma val_canonize {v : nat → int} :
  ∀ {t : preterm}, (canonize t).val v = t.val v
| (& i) :=
  by simp only [preterm.val, add_zero, term.val, canonize, coeffs.val_nil]
| (i ** n)   :=
  begin
    simp only [coeffs.val_set, canonize,
      preterm.val, zero_add, term.val],
    split_ifs with h1 h2,
    { simp only [one_mul, h1] },
    { simp only [neg_mul_eq_neg_mul_symm, one_mul, h2] },
    { rw mul_comm }
  end
| (t +* s) :=
  by simp only [canonize, val_canonize,
     term.val_add, preterm.val]

end int

end omega
