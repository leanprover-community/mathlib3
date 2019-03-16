/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.clause 

@[omega] def lin_comb : list term → list nat → term 
| [] []     := ⟨0,[]⟩ 
| [] (_::_) := ⟨0,[]⟩ 
| (_::_) [] := ⟨0,[]⟩ 
| (t::ts) (n::ns) := term.add (t.mul ↑n) (lin_comb ts ns)

lemma lin_comb_holds {v} :
  ∀ {ts} ns, (∀ t ∈ ts, 0 ≤ term.val v t) → (0 ≤ (lin_comb ts ns).val v) 
| [] []     h := by simp_omega
| [] (_::_) h := by simp_omega
| (_::_) [] h := by simp_omega
| (t::ts) (n::ns) h :=
  begin
    simp_omega, apply add_nonneg, 
    { apply mul_nonneg,
      apply int.coe_nat_nonneg,
      apply h _ (or.inl rfl) },
    { apply lin_comb_holds, 
      apply list.forall_mem_of_forall_mem_cons h }
  end

def unsat_lin_comb (ts ns) : Prop :=
(lin_comb ts ns).fst < 0 ∧ ∀ x ∈ (lin_comb ts ns).snd, x = (0 : int)

lemma unsat_lin_comb_of (ts ns) : 
(lin_comb ts ns).fst < 0 → 
(∀ x ∈ (lin_comb ts ns).snd, x = (0 : int)) → 
unsat_lin_comb ts ns := 
begin intros h1 h2, exact ⟨h1,h2⟩ end

lemma unsat_of_unsat_lin_comb (ns les) :
  (unsat_lin_comb les ns) → clause.unsat ([], les) :=
begin
  intros h1 h2, cases h2 with v h2, 
  have h3 := lin_comb_holds ns h2.right,
  cases h1 with hl hr, 
  cases (lin_comb les ns) with b as,
  simp_omega at h3, 
  rw [coeffs.val_eq_zero hr, add_zero, ← not_lt] at h3,
  apply h3 hl 
end