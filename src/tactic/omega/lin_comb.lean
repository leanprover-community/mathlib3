/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Linear combination of constraints. -/

import tactic.omega.clause

namespace omega

/-- Linear combination of constraints. The second
    argument is the list of constraints, and the first
    argument is the list of conefficients by which the
    constraints are multiplied -/
@[simp] def lin_comb : list nat → list term → term
| [] []     := ⟨0,[]⟩
| [] (_::_) := ⟨0,[]⟩
| (_::_) [] := ⟨0,[]⟩
| (n::ns) (t::ts) := term.add (t.mul ↑n) (lin_comb ns ts)

lemma lin_comb_holds {v : nat → int} :
  ∀ {ts} ns, (∀ t ∈ ts, 0 ≤ term.val v t) → (0 ≤ (lin_comb ns ts).val v)
| [] []     h := by simp only [add_zero, term.val, lin_comb, coeffs.val_nil]
| [] (_::_) h := by simp only [add_zero, term.val, lin_comb, coeffs.val_nil]
| (_::_) [] h := by simp only [add_zero, term.val, lin_comb, coeffs.val_nil]
| (t::ts) (n::ns) h :=
  begin
    have : 0 ≤ ↑n * term.val v t + term.val v (lin_comb ns ts),
    { apply add_nonneg,
      { apply mul_nonneg,
        apply int.coe_nat_nonneg,
        apply h _ (or.inl rfl) },
      { apply lin_comb_holds,
        apply list.forall_mem_of_forall_mem_cons h } },
    simpa only [lin_comb, term.val_mul, term.val_add],
  end

/-- `unsat_lin_comb ns ts` asserts that the linear combination
    `lin_comb ns ts` is unsatisfiable  -/
def unsat_lin_comb (ns : list nat) (ts : list term) : Prop :=
(lin_comb ns ts).fst < 0 ∧ ∀ x ∈ (lin_comb ns ts).snd, x = (0 : int)

lemma unsat_lin_comb_of (ns : list nat) (ts : list term) :
(lin_comb ns ts).fst < 0 →
(∀ x ∈ (lin_comb ns ts).snd, x = (0 : int)) →
unsat_lin_comb ns ts :=
by {intros h1 h2, exact ⟨h1,h2⟩}

lemma unsat_of_unsat_lin_comb
  (ns : list nat) (ts : list term) :
  (unsat_lin_comb ns ts) → clause.unsat ([], ts) :=
begin
  intros h1 h2, cases h2 with v h2,
  have h3 := lin_comb_holds ns h2.right,
  cases h1 with hl hr,
  cases (lin_comb ns ts) with b as,
  unfold term.val at h3,
  rw [coeffs.val_eq_zero hr, add_zero, ← not_lt] at h3,
  apply h3 hl
end

end omega
