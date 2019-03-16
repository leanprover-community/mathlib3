/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.term

@[reducible] def clause := (list term) × (list term)

namespace clause

def holds (v) : clause → Prop 
| (eqs,les) :=
  ( (∀ t : term, t ∈ eqs → 0 = term.val v t) 
    ∧ (∀ t : term, t ∈ les → 0 ≤ term.val v t) )

def sat (c : clause) : Prop :=
  ∃ v : nat → int, holds v c

def unsat (c : clause) : Prop := ¬ c.sat 

def append (c1 c2 : clause) : clause :=
(c1.fst ++ c2.fst, c1.snd ++ c2.snd)

def holds_append {v c1 c2} : 
holds v c1 → holds v c2 → holds v (append c1 c2) := 
begin
  intros h1 h2, 
  cases c1 with eqs1 les1,
  cases c2 with eqs2 les2,
  cases h1, cases h2,
  constructor; rw list.forall_mem_append; 
  constructor; assumption,
end

end clause

def clauses.sat (ps : list clause) : Prop := 
∃ c ∈ ps, clause.sat c  

def clauses.unsat (ps) : Prop := ¬ clauses.sat ps

lemma clauses.unsat_nil : clauses.unsat [] := 
begin intro h1, rcases h1 with ⟨c,h1,h2⟩, cases h1 end

lemma clauses.unsat_cons (p ps) : 
  clause.unsat p → clauses.unsat ps → 
  clauses.unsat (p::ps) | h1 h2 h3 := 
begin
  simp only [clauses.sat] at h3,
  rw list.exists_mem_cons_iff at h3, 
  cases h3; contradiction,
end