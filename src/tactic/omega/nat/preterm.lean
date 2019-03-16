/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.term

open tactic

namespace nat 

@[derive has_reflect, derive decidable_eq]
inductive preterm : Type
| cst : nat → preterm 
| var : nat → nat → preterm
| add : preterm → preterm → preterm 
| sub : preterm → preterm → preterm 

notation `&` k := preterm.cst k
infix `**` : 300 := preterm.var 
notation t `+*` s := preterm.add t s
notation t `-*` s := preterm.sub t s

namespace preterm 

meta def induce (tac : tactic unit := tactic.skip) : tactic unit := 
`[ intro t, induction t with m m n t s iht ihs t s iht ihs; tac]

def val (v : nat → nat) : preterm → nat 
| (& i) := i
| (i ** n) := 
  if i = 1 
  then v n
  else (v n) * i
| (t1 +* t2) := t1.val + t2.val 
| (t1 -* t2) := t1.val - t2.val 

@[omega] lemma val_const {v m} : (& m).val v = m := rfl

@[omega] lemma val_var {v m n} :
  (m ** n).val v = m * (v n) :=
begin
  simp only [val], by_cases h1 : m = 1,
  rw [if_pos h1, h1, one_mul],
  rw [if_neg h1, mul_comm], 
end

@[omega] lemma val_add {v t s} : (t +* s).val v = t.val v + s.val v := rfl

@[omega] lemma val_sub {v t s} : (t -* s).val v = t.val v - s.val v := rfl

def fresh_index : preterm → nat 
| (& _)      := 0
| (i ** n)   := n + 1
| (t1 +* t2) := max t1.fresh_index t2.fresh_index 
| (t1 -* t2) := max t1.fresh_index t2.fresh_index 

def val_constant (v w : nat → nat) :
  ∀ t : preterm, (∀ x < t.fresh_index, v x = w x) → 
  t.val v = t.val w 
| (& n)      h1 := rfl 
| (m ** n)   h1 := 
  begin
    simp_omega, apply congr_arg (λ y, m * y),
    apply h1 _ (lt_add_one _) 
  end 
| (t +* s) h1 := 
  begin
    simp_omega, 
    have ht := val_constant t 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _))),
    have hs := val_constant s 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _))),
    rw [ht, hs]
  end 
| (t -* s) h1 := 
  begin
    simp_omega, 
    have ht := val_constant t 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _))),
    have hs := val_constant s 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _))),
    rw [ht, hs]
  end 


def repr : preterm → string 
| (& i)      := i.repr
| (i ** n)   := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
| (t1 -* t2) := "(" ++ t1.repr ++ " - " ++ t2.repr ++ ")"

@[omega] def add_one (t : preterm) : preterm := t +* (&1)

def sub_free : preterm → Prop 
| (& m)    := true
| (m ** n) := true
| (t +* s) := t.sub_free ∧ s.sub_free
| (_ -* _) := false

end preterm

@[omega] def canonize : preterm → term 
| (& m)    := ⟨↑m,[]⟩  
| (m ** n) := ⟨0,[]{n ↦ ↑m}⟩ 
| (t +* s) := term.add (canonize t) (canonize s)
| (_ -* _) := ⟨0,[]⟩ -- Irr.

@[omega] lemma val_canonize {v : nat → nat} : 
  ∀ {t : preterm}, t.sub_free → 
  (canonize t).val (λ x, ↑(v x)) = t.val v
| (& i) h1 := by simp_omega
| (i ** n) h1 := 
  begin simp_omega, rw ← int.coe_nat_mul end
| (t +* s) h1 := 
  by simp_omega [val_canonize h1.left, 
    val_canonize h1.right, int.coe_nat_add]

end nat
