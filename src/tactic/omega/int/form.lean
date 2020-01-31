/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Linear integer arithmetic formulas in pre-normalized form. -/

import tactic.omega.int.preterm

namespace omega
namespace int

meta inductive exprform
| eq  : exprterm → exprterm → exprform
| le  : exprterm → exprterm → exprform
| not : exprform → exprform
| or  : exprform → exprform → exprform
| and : exprform → exprform → exprform

@[derive has_reflect]
inductive preform
| eq  : preterm → preterm → preform
| le  : preterm → preterm → preform
| not : preform → preform
| or  : preform → preform → preform
| and : preform → preform → preform

localized "notation x ` =* ` y := omega.int.preform.eq x y" in omega.int
localized "notation x ` ≤* ` y := omega.int.preform.le x y" in omega.int
localized "notation `¬* ` p   := omega.int.preform.not p" in omega.int
localized "notation p ` ∨* ` q := omega.int.preform.or p q" in omega.int
localized "notation p ` ∧* ` q := omega.int.preform.and p q" in omega.int

namespace preform

@[simp] def holds (v : nat → int) : preform → Prop
| (t =* s) := t.val v = s.val v
| (t ≤* s) := t.val v ≤ s.val v
| (¬* p)   := ¬ p.holds
| (p ∨* q) := p.holds ∨ q.holds
| (p ∧* q) := p.holds ∧ q.holds

end preform

@[simp] def univ_close (p : preform) : (nat → int) → nat → Prop
| v 0     := p.holds v
| v (k+1) := ∀ i : int, univ_close (update_zero i v) k

namespace preform

/-- Return the de Brujin index of a fresh variable that does not
    occur anywhere in a given LIA formula -/
def fresh_index : form → nat
| (t =* s) := max t.fresh_index s.fresh_index
| (t ≤* s) := max t.fresh_index s.fresh_index
| (¬* p)   := p.fresh_index
| (p ∨* q) := max p.fresh_index q.fresh_index
| (p ∧* q) := max p.fresh_index q.fresh_index

/-- A LIA formula is valid if it holds under all valuations -/
def valid (p : form) : Prop :=
∀ v, holds v p

/-- A LIA formula is satisfiable if it holds under some valuation -/
def sat (p : form) : Prop :=
∃ v, holds v p

/-- A LIA formula p implies another LIA formula q if,
    under any valuation, q holds whenever p holds -/
def implies (p q : form) : Prop :=
∀ v, (holds v p → holds v q)

/-- A LIA formula p is equivalent to another LIA formula q if,
    under any valuation, p holds iff and only if q holds -/
def equiv (p q : form) : Prop :=
∀ v, (holds v p ↔ holds v q)

lemma sat_of_implies_of_sat {p q : preform} :
  implies p q → sat p → sat q :=
begin intros h1 h2, apply exists_imp_exists h1 h2 end

lemma sat_or {p q : preform} :
  sat (p ∨* q) ↔ sat p ∨ sat q :=
begin
  constructor; intro h1,
  { cases h1 with v h1, cases h1 with h1 h1;
    [left,right]; refine ⟨v,_⟩; assumption },
  { cases h1 with h1 h1; cases h1 with v h1;
    refine ⟨v,_⟩; [left,right]; assumption }
end

/-- A LIA formula is unsatisfiable if does not hold under any valuation -/
def unsat (p : form) : Prop := ¬ sat p

/-- repr for LIA formulas -/
def repr : form → string
| (t =* s) := "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
| (t ≤* s) := "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
| (¬* p)   := "¬" ++ p.repr
| (p ∨* q) := "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"

instance has_repr : has_repr preform := ⟨repr⟩
meta instance has_to_format : has_to_format preform := ⟨λ x, x.repr⟩

end preform

lemma univ_close_of_valid {p : preform} :
  ∀ {m v}, p.valid → univ_close p v m
| 0 v h1     := h1 _
| (m+1) v h1 := λ i, univ_close_of_valid h1

lemma valid_of_unsat_not {p : preform} : (¬*p).unsat → p.valid :=
begin
  simp only [preform.sat, preform.unsat, preform.valid, preform.holds],
  rw classical.not_exists_not, intro h, assumption
end

/-- Tactic for setting up proof by induction over preforms. -/
meta def preform.induce (t : tactic unit := tactic.skip) : tactic unit :=
`[ intro p, induction p with t s t s p ih p q ihp ihq p q ihp ihq; t]

end int

end omega
