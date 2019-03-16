/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.term

namespace int 

@[derive has_reflect]
inductive preterm : Type
| cst : int → preterm 
| var : int → nat → preterm
| add : preterm → preterm → preterm 

notation `&` k := preterm.cst k
infix `**` : 300 := preterm.var 
notation t `+*` s := preterm.add t s

namespace preterm 

@[omega] def val (v : nat → int) : preterm → int 
| (& i) := i
| (i ** n) := 
  if i = 1 
  then v n
  else if i = -1 
       then -(v n) 
       else (v n) * i
| (t1 +* t2) := t1.val + t2.val 

def fresh_index : preterm → nat 
| (& _) := 0
| (i ** n) := n + 1
| (t1 +* t2) := max t1.fresh_index t2.fresh_index 

@[omega] def add_one (t : preterm) : preterm := t +* (&1)

def repr : preterm → string 
| (& i) := i.repr
| (i ** n) := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"

end preterm

@[omega] def canonize : preterm → term 
| (& i)      := ⟨i,[]⟩  
| (i ** n)   := ⟨0,[]{n ↦ i}⟩ 
| (t1 +* t2) := term.add (canonize t1) (canonize t2)

@[omega] lemma val_canonize {v} : ∀ {t}, (canonize t).val v = t.val v 
| (& i)      := by simp_omega
| (i ** n)   := 
  begin 
    simp_omega, apply ite_rec; intro h1,
    { simp only [one_mul, h1] },
    { apply ite_rec; intro h2, 
      { rw h2, simp },
      { rw mul_comm } }
  end
| (t1 +* t2) := by simp_omega [@val_canonize t1, @val_canonize t2]

end int
