/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Definition of linear constrain clauses. -/

import tactic.omega.term

namespace omega

/-- (([t₁,...tₘ],[s₁,...,sₙ]) : clause) encodes the constraints
0 = ⟦t₁⟧ ∧ ... ∧ 0 = ⟦tₘ⟧ ∧ 0 ≤ ⟦s₁⟧ ∧ ... ∧ 0 ≤ ⟦sₙ⟧, where
⟦t⟧ is the value of (t : term). -/
@[reducible] def clause := (list term) × (list term)

namespace clause

/-- holds v c := clause c holds under valuation v -/
def holds (v : nat → int) : clause → Prop
| (eqs,les) :=
  ( (∀ t : term, t ∈ eqs → 0 = term.val v t)
    ∧ (∀ t : term, t ∈ les → 0 ≤ term.val v t) )

/-- sat c := there exists a valuation v under which c holds -/
def sat (c : clause) : Prop :=
  ∃ v : nat → int, holds v c

/-- unsat c := there is no valuation v under which c holds -/
def unsat (c : clause) : Prop := ¬ c.sat

/-- append two clauses by elementwise appending -/
def append (c1 c2 : clause) : clause :=
(c1.fst ++ c2.fst, c1.snd ++ c2.snd)

lemma holds_append {v : nat → int} {c1 c2 : clause} :
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

/-- There exists a satisfiable clause c in argument -/
def clauses.sat (cs : list clause) : Prop :=
∃ c ∈ cs, clause.sat c

/-- There is no satisfiable clause c in argument -/
def clauses.unsat (cs : list clause) : Prop := ¬ clauses.sat cs

lemma clauses.unsat_nil : clauses.unsat [] :=
begin intro h1, rcases h1 with ⟨c,h1,h2⟩, cases h1 end

lemma clauses.unsat_cons (c : clause) (cs : list clause) :
  clause.unsat c → clauses.unsat cs →
  clauses.unsat (c::cs) | h1 h2 h3 :=
begin
  unfold clauses.sat at h3,
  rw list.exists_mem_cons_iff at h3,
  cases h3; contradiction,
end

end omega
