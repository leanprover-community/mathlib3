/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Linear natural number arithmetic formulas in pre-normalized form.
-/

import tactic.omega.nat.preterm

namespace omega

namespace nat

@[derive has_reflect]
inductive form
| eq  : preterm → preterm → form
| le  : preterm → preterm → form
| not : form → form
| or  : form → form → form
| and : form → form → form

localized "notation x ` =* ` y := omega.nat.form.eq x y" in omega.nat
localized "notation x ` ≤* ` y := omega.nat.form.le x y" in omega.nat
localized "notation `¬* ` p   := omega.nat.form.not p" in omega.nat
localized "notation p ` ∨* ` q := omega.nat.form.or p q" in omega.nat
localized "notation p ` ∧* ` q := omega.nat.form.and p q" in omega.nat

namespace form

@[simp] def holds (v : nat → nat) : form → Prop
| (t =* s) := t.val v = s.val v
| (t ≤* s) := t.val v ≤ s.val v
| (¬* p)   := ¬ p.holds
| (p ∨* q) := p.holds ∨ q.holds
| (p ∧* q) := p.holds ∧ q.holds

end form

@[simp] def univ_close (p : form) : (nat → nat) → nat → Prop
| v 0     := p.holds v
| v (k+1) := ∀ i : nat, univ_close (update_zero i v) k

namespace form

def neg_free : form → Prop
| (t =* s) := true
| (t ≤* s) := true
| (p ∨* q) := neg_free p ∧ neg_free q
| (p ∧* q) := neg_free p ∧ neg_free q
| _        := false

def sub_free : form → Prop
| (t =* s) := t.sub_free ∧ s.sub_free
| (t ≤* s) := t.sub_free ∧ s.sub_free
| (¬* p)   := p.sub_free
| (p ∨* q) := p.sub_free ∧ q.sub_free
| (p ∧* q) := p.sub_free ∧ q.sub_free

def fresh_index : form → nat
| (t =* s) := max t.fresh_index s.fresh_index
| (t ≤* s) := max t.fresh_index s.fresh_index
| (¬* p)   := p.fresh_index
| (p ∨* q) := max p.fresh_index q.fresh_index
| (p ∧* q) := max p.fresh_index q.fresh_index

lemma holds_constant {v w : nat → nat} :
  ∀ p : form,
  ( (∀ x < p.fresh_index, v x = w x) →
    (p.holds v ↔ p.holds w) )
| (t =* s) h1 :=
  begin
    simp only [holds],
    apply pred_mono_2;
    apply preterm.val_constant;
    intros x h2; apply h1 _ (lt_of_lt_of_le h2 _),
    apply le_max_left, apply le_max_right
  end
| (t ≤* s) h1 :=
  begin
    simp only [holds],
    apply pred_mono_2;
    apply preterm.val_constant;
    intros x h2; apply h1 _ (lt_of_lt_of_le h2 _),
    apply le_max_left, apply le_max_right
  end
| (¬* p)   h1 :=
  begin
    apply not_iff_not_of_iff,
    apply holds_constant p h1
  end
| (p ∨* q) h1 :=
  begin
    simp only [holds],
    apply pred_mono_2';
    apply holds_constant;
    intros x h2; apply h1 _ (lt_of_lt_of_le h2 _),
    apply le_max_left, apply le_max_right
  end
| (p ∧* q) h1 :=
  begin
    simp only [holds],
    apply pred_mono_2';
    apply holds_constant;
    intros x h2; apply h1 _ (lt_of_lt_of_le h2 _),
    apply le_max_left, apply le_max_right
  end

def valid (p : form) : Prop :=
∀ v, holds v p

def sat (p : form) : Prop :=
∃ v, holds v p

def implies (p q : form) : Prop :=
∀ v, (holds v p → holds v q)

def equiv (p q : form) : Prop :=
∀ v, (holds v p ↔ holds v q)

lemma sat_of_implies_of_sat {p q : form} :
  implies p q → sat p → sat q :=
begin intros h1 h2, apply exists_imp_exists h1 h2 end

lemma sat_or {p q : form} :
  sat (p ∨* q) ↔ sat p ∨ sat q :=
begin
  constructor; intro h1,
  { cases h1 with v h1, cases h1 with h1 h1;
    [left,right]; refine ⟨v,_⟩; assumption },
  { cases h1 with h1 h1; cases h1 with v h1;
    refine ⟨v,_⟩; [left,right]; assumption }
end

def unsat (p : form) : Prop := ¬ sat p

def repr : form → string
| (t =* s) := "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
| (t ≤* s) := "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
| (¬* p)   := "¬" ++ p.repr
| (p ∨* q) := "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"

instance has_repr : has_repr form := ⟨repr⟩
meta instance has_to_format : has_to_format form := ⟨λ x, x.repr⟩

end form

lemma univ_close_of_valid {p : form} :
  ∀ {m : nat} {v : nat → nat}, p.valid → univ_close p v m
| 0 v h1     := h1 _
| (m+1) v h1 := λ i, univ_close_of_valid h1

lemma valid_of_unsat_not {p : form} : (¬*p).unsat → p.valid :=
begin
  simp only [form.sat, form.unsat, form.valid, form.holds],
  rw classical.not_exists_not, intro h, assumption
end

meta def form.induce (t : tactic unit := tactic.skip) : tactic unit :=
`[ intro p, induction p with t s t s p ih p q ihp ihq p q ihp ihq; t ]

end nat

end omega
