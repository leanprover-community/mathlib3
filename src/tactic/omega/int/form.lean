/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
Linear integer arithmetic formulas in pre-normalized form.
-/

import tactic.omega.int.preterm

namespace omega
namespace int

/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
meta inductive exprform
| eq  : exprterm → exprterm → exprform
| le  : exprterm → exprterm → exprform
| not : exprform → exprform
| or  : exprform → exprform → exprform
| and : exprform → exprform → exprform

/-- Intermediate shadow syntax for LIA formulas that includes non-canonical terms -/
@[derive has_reflect, derive inhabited]
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

/-- Evaluate a preform into prop using the valuation v. -/
@[simp] def holds (v : nat → int) : preform → Prop
| (t =* s) := t.val v = s.val v
| (t ≤* s) := t.val v ≤ s.val v
| (¬* p)   := ¬ p.holds
| (p ∨* q) := p.holds ∨ q.holds
| (p ∧* q) := p.holds ∧ q.holds

end preform

/-- univ_close p n := p closed by prepending n universal quantifiers -/
@[simp] def univ_close (p : preform) : (nat → int) → nat → Prop
| v 0     := p.holds v
| v (k+1) := ∀ i : int, univ_close (update_zero i v) k

namespace preform

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preform → nat
| (t =* s) := max t.fresh_index s.fresh_index
| (t ≤* s) := max t.fresh_index s.fresh_index
| (¬* p)   := p.fresh_index
| (p ∨* q) := max p.fresh_index q.fresh_index
| (p ∧* q) := max p.fresh_index q.fresh_index

/-- All valuations satisfy argument -/
def valid (p : preform) : Prop :=
∀ v, holds v p

/-- There exists some valuation that satisfies argument -/
def sat (p : preform) : Prop :=
∃ v, holds v p

/-- implies p q := under any valuation, q holds if p holds -/
def implies (p q : preform) : Prop :=
∀ v, (holds v p → holds v q)

/-- equiv p q := under any valuation, p holds iff q holds -/
def equiv (p q : preform) : Prop :=
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

/-- There does not exist any valuation that satisfies argument -/
def unsat (p : preform) : Prop := ¬ sat p

def repr : preform → string
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
  rw not_exists_not, intro h, assumption
end

/-- Tactic for setting up proof by induction over preforms. -/
meta def preform.induce (t : tactic unit := tactic.skip) : tactic unit :=
`[ intro p, induction p with t s t s p ih p q ihp ihq p q ihp ihq; t]

end int

end omega
