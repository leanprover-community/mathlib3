/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for finding a sequence of equality
elimination rules for a given set of constraints. -/

import tactic.omega.eq_elim

variables {α β : Type}

open tactic

namespace omega

/-- The state of equality elimination proof search. `eqs` is the list of
    equality constraints, and each `t ∈ eqs` represents the constraint `0 = t`.
    Similarly, `les` is the list of inequality constraints, and each `t ∈ eqs`
    represents the constraint `0 < t`. `ees` is the sequence of equality
    elimination steps that have been used so far to obtain the current set of
    constraints. The list `ees` grows over time until `eqs` becomes empty. -/
structure ee_state :=
(eqs : list term)
(les : list term)
(ees : list ee)

@[reducible] meta def eqelim := state_t ee_state tactic

meta def abort {α : Type} : eqelim α := ⟨λ x, failed⟩

private meta def mk_eqelim_state
  (eqs les : list term) : tactic ee_state :=
return (ee_state.mk eqs les [])

/-- Get the current list of equality constraints. -/
meta def get_eqs : eqelim (list term) := ee_state.eqs <$> get
/-- Get the current list of inequality constraints. -/
meta def get_les : eqelim (list term) := ee_state.les <$> get
/-- Get the current sequence of equality elimiation steps. -/
meta def get_ees : eqelim (list ee)   := ee_state.ees <$> get

/-- Update the list of equality constraints. -/
meta def set_eqs (eqs : list term) : eqelim unit := modify $ λ s, {eqs := eqs, ..s}
/-- Update the list of inequality constraints. -/
meta def set_les (les : list term) : eqelim unit := modify $ λ s, {les := les, ..s}
/-- Update the sequence of equality elimiation steps. -/
meta def set_ees (es : list ee) : eqelim unit := modify $ λ s, {ees := es, ..s}

/-- Add a new step to the sequence of equality elimination steps. -/
meta def add_ee (e : ee) : eqelim unit := do
es ← get_ees, set_ees (es ++ [e])

/-- Return the first equality constraint in the current list of
    equality constraints. The returned constraint is 'popped' and
    no longer available in the state. -/
meta def head_eq : eqelim term :=
do eqs ← get_eqs,
   match eqs with
   | []         := abort
   | (eq::eqs') := set_eqs eqs' >> pure eq
   end

meta def run {α : Type} (eqs les : list term) (r : eqelim α) : tactic α :=
prod.fst <$> (mk_eqelim_state eqs les >>= r.run)

/-- If `t1` succeeds and returns a value, 'commit' to that choice and
    run `t3` with the returned value as argument. Do not backtrack
    to try `t2` even if `t3` fails. If `t1` fails outright, run `t2`. -/
meta def ee_commit (t1 : eqelim α) (t2 : eqelim β)
  (t3 : α → eqelim β) : eqelim β :=
do x ← ((t1 >>= return ∘ some) <|> return none),
   match x with
   | none     := t2
   | (some a) := t3 a
   end

local notation t1 `!>>=` t2 `;` t3 := ee_commit t1 t2 t3

private meta def of_tactic {α : Type} : tactic α → eqelim α := state_t.lift

/-- GCD of all elements of the list. -/
def gcd : list int → nat
| []      := 0
| (i::is) := nat.gcd i.nat_abs (gcd is)

/-- GCD of all coefficients in a term. -/
meta def get_gcd (t : term) : eqelim int :=
pure ↑(gcd t.snd)

/-- Divide a term by an integer if the integer divides
    the constant component of the term. It is assumed that
    the integer also divides all coefficients of the term. -/
meta def factor (i : int) (t : term) : eqelim term :=
if i ∣ t.fst
then add_ee (ee.factor i) >> pure (t.div i)
else abort

/-- If list has a nonzero element, return the minimum element
(by absolute value) with its index. Otherwise, return none. -/
meta def find_min_coeff_core : list int → eqelim (int × nat)
| []      := abort
| (i::is) := (do
  (j,n) ← find_min_coeff_core is,
  if i ≠ 0 ∧ i.nat_abs ≤ j.nat_abs
  then pure (i,0)
  else pure (j,n+1)) <|>
  (if i = (0 : int) then abort else pure (i,0))

/-- Find and return the smallest coefficient (by absolute value) in a term,
    along with the coefficient's variable index and the term itself.
    If the coefficient is negative, negate both the coefficient and the term
    before returning them. -/
meta def find_min_coeff (t : term) : eqelim (int × nat × term) :=
do (i,n) ← find_min_coeff_core t.snd,
   if 0 < i
   then pure (i,n,t)
   else add_ee (ee.neg) >> pure (-i,n,t.neg)

/-- Find an appropriate equality elimination step for the
    current state and apply it. -/
meta def elim_eq : eqelim unit := do
t ← head_eq,
i ← get_gcd t,
    factor i t !>>= (set_eqs [] >> add_ee (ee.nondiv i)) ;
λ s, find_min_coeff s !>>= add_ee ee.drop ;
λ ⟨i, n, u⟩,
if i = 1
then do eqs ← get_eqs,
        les ← get_les,
              set_eqs (eqs.map (cancel n u)),
              set_les (les.map (cancel n u)),
              add_ee (ee.cancel n)
else let v : term := coeffs_reduce n u.fst u.snd in
     let r : term := rhs n u.fst u.snd in
     do eqs ← get_eqs,
        les ← get_les,
              set_eqs (v::eqs.map (subst n r)),
              set_les (les.map (subst n r)),
              add_ee (ee.reduce n),
              elim_eq

/-- Find and return the sequence of steps for eliminating
    all equality constraints in the current state. -/
meta def elim_eqs : eqelim (list ee) :=
elim_eq !>>= get_ees ; λ _, elim_eqs

/-- Given a linear constrain clause, return a list of steps for eliminating its equality constraints. -/
meta def find_ees : clause → tactic (list ee)
| (eqs,les) := run eqs les elim_eqs

end omega
