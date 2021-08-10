/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
DNF transformation.
-/

import tactic.omega.clause
import tactic.omega.nat.form

namespace omega
namespace nat

open_locale omega.nat

@[simp] def dnf_core : preform → list clause
| (p ∨* q) := (dnf_core p) ++ (dnf_core q)
| (p ∧* q) :=
  (list.product (dnf_core p) (dnf_core q)).map
  (λ pq, clause.append pq.fst pq.snd)
| (t =* s) :=
  [([term.sub (canonize s) (canonize t)],[])]
| (t ≤* s) := [([],[term.sub (canonize s) (canonize t)])]
| (¬* _)   := []

lemma exists_clause_holds_core {v : nat → nat} :
  ∀ {p : preform}, p.neg_free → p.sub_free → p.holds v →
  ∃ c ∈ (dnf_core p), clause.holds (λ x, ↑(v x)) c :=
begin
  preform.induce `[intros h1 h0 h2],
  { apply list.exists_mem_cons_of,
    constructor, rw list.forall_mem_singleton,
    cases h0 with ht hs,
    simp only [val_canonize ht, val_canonize hs,
      term.val_sub, preform.holds, sub_eq_add_neg] at *,
    rw [h2, add_neg_self], apply list.forall_mem_nil },
  { apply list.exists_mem_cons_of,
    constructor,
    apply list.forall_mem_nil,
    rw list.forall_mem_singleton,
    simp only [val_canonize (h0.left), val_canonize (h0.right),
      term.val_sub, preform.holds, sub_eq_add_neg] at *,
    rw [←sub_eq_add_neg, le_sub, sub_zero, int.coe_nat_le],
    assumption },
  { cases h1 },
  { cases h2 with h2 h2;
    [ {cases (ihp h1.left h0.left h2) with c h3},
      {cases (ihq h1.right h0.right h2) with c h3}];
    cases h3 with h3 h4;
    refine ⟨c, list.mem_append.elim_right _, h4⟩;
    [left,right]; assumption },
  { rcases (ihp h1.left h0.left h2.left) with ⟨cp, hp1, hp2⟩,
    rcases (ihq h1.right h0.right h2.right) with ⟨cq, hq1, hq2⟩,
    refine ⟨clause.append cp cq, ⟨_, clause.holds_append hp2 hq2⟩⟩,
    simp only [dnf_core, list.mem_map],
    refine ⟨(cp,cq),⟨_,rfl⟩⟩,
    rw list.mem_product,
    constructor; assumption }
end

def term.vars_core (is : list int) : list bool :=
is.map (λ i, if i = 0 then ff else tt)

/-- Return a list of bools that encodes which variables have nonzero coefficients -/
def term.vars (t : term) : list bool :=
term.vars_core t.snd

def bools.or : list bool → list bool → list bool
| []        bs2       := bs2
| bs1       []        := bs1
| (b1::bs1) (b2::bs2) := (b1 || b2)::(bools.or bs1 bs2)

/-- Return a list of bools that encodes which variables have nonzero coefficients in any one of the
input terms. -/
def terms.vars : list term → list bool
| []      := []
| (t::ts) := bools.or (term.vars t) (terms.vars ts)

open_locale list.func -- get notation for list.func.set

def nonneg_consts_core : nat → list bool → list term
| _ [] := []
| k (ff::bs) := nonneg_consts_core (k+1) bs
| k (tt::bs) := ⟨0, [] {k ↦ 1}⟩::nonneg_consts_core (k+1) bs

def nonneg_consts (bs : list bool) : list term :=
nonneg_consts_core 0 bs

def nonnegate : clause → clause | (eqs,les) :=
let xs := terms.vars eqs in
let ys := terms.vars les in
let bs := bools.or xs ys in
(eqs, nonneg_consts bs ++ les)

/-- DNF transformation -/
def dnf (p : preform) : list clause :=
(dnf_core p).map nonnegate

lemma holds_nonneg_consts_core {v : nat → int} (h1 : ∀ x, 0 ≤ v x) :
  ∀ m bs, (∀ t ∈ (nonneg_consts_core m bs), 0 ≤ term.val v t)
| _ []       := λ _ h2, by cases h2
| k (ff::bs) := holds_nonneg_consts_core (k+1) bs
| k (tt::bs) :=
  begin
    simp only [nonneg_consts_core],
    rw list.forall_mem_cons,
    constructor,
    { simp only [term.val, one_mul, zero_add, coeffs.val_set],
      apply h1 },
    { apply holds_nonneg_consts_core (k+1) bs }
  end

lemma holds_nonneg_consts {v : nat → int} {bs : list bool} :
  (∀ x, 0 ≤ v x) → (∀ t ∈ (nonneg_consts bs), 0 ≤ term.val v t)
| h1 :=
by apply holds_nonneg_consts_core h1

lemma exists_clause_holds {v : nat → nat} {p : preform} :
  p.neg_free → p.sub_free → p.holds v →
  ∃ c ∈ (dnf p), clause.holds (λ x, ↑(v x)) c :=
begin
  intros h1 h2 h3,
  rcases (exists_clause_holds_core h1 h2 h3) with ⟨c,h4,h5⟩,
  existsi (nonnegate c),
  have h6 : nonnegate c ∈ dnf p,
  { simp only [dnf], rw list.mem_map,
    refine ⟨c,h4,rfl⟩ },
  refine ⟨h6,_⟩, cases c with eqs les,
  simp only [nonnegate, clause.holds],
  constructor, apply h5.left,
  rw list.forall_mem_append,
  apply and.intro (holds_nonneg_consts _) h5.right,
  assume x,
  apply int.coe_nat_nonneg
end

lemma exists_clause_sat {p : preform} :
  p.neg_free → p.sub_free →
  p.sat → ∃ c ∈ (dnf p), clause.sat c :=
begin
  intros h1 h2 h3, cases h3 with v h3,
  rcases (exists_clause_holds h1 h2 h3) with ⟨c,h4,h5⟩,
  refine ⟨c,h4,_,h5⟩
end

lemma unsat_of_unsat_dnf (p : preform) :
  p.neg_free → p.sub_free → clauses.unsat (dnf p) → p.unsat :=
begin
  intros hnf hsf h1 h2, apply h1,
  apply exists_clause_sat hnf hsf h2
end

end nat

end omega
