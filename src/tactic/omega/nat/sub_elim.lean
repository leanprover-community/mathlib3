/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Subtraction elimination for linear natural number arithmetic.
Works by repeatedly rewriting goals of the preform `P[t-s]` into
`P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh. -/

import tactic.omega.nat.form

namespace omega
namespace nat

open_locale omega.nat

namespace preterm

/-- Find subtraction inside preterm and return its operands -/
def sub_terms : preterm → option (preterm × preterm)
| (& i)      := none
| (i ** n)   := none
| (t +* s) := t.sub_terms <|> s.sub_terms
| (t -* s) := t.sub_terms <|> s.sub_terms <|> some (t,s)

/-- Find (t - s) inside a preterm and replace it with variable k -/
def sub_subst (t s : preterm) (k : nat) : preterm → preterm
| t@(& m)    := t
| t@(m ** n) := t
| (x +* y) := x.sub_subst +* y.sub_subst
| (x -* y) :=
  if x = t ∧ y = s then (1 ** k)
  else x.sub_subst -* y.sub_subst

lemma val_sub_subst {k : nat} {x y : preterm} {v : nat → nat} :
  ∀ {t : preterm}, t.fresh_index ≤ k →
  (sub_subst x y k t).val (update k (x.val v - y.val v) v) = t.val v
| (& m)    h1 := rfl
| (m ** n) h1 :=
  begin
    have h2 : n ≠ k := ne_of_lt h1,
    simp only [sub_subst, preterm.val],
    rw update_eq_of_ne _ h2,
 end
| (t +* s) h1 :=
  begin
    simp only [sub_subst, val_add], apply fun_mono_2;
    apply val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (t -* s) h1 :=
  begin
    simp only [sub_subst, val_sub],
    by_cases h2 : t = x ∧ s = y,
    { rw if_pos h2, simp only [val_var, one_mul],
      rw [update_eq, h2.left, h2.right] },
    { rw if_neg h2,
      simp only [val_sub, sub_subst],
      apply fun_mono_2;
      apply val_sub_subst (le_trans _ h1),
      apply le_max_left, apply le_max_right, }
  end

end preterm

namespace preform

/-- Find subtraction inside preform and return its operands -/
def sub_terms : preform → option (preterm × preterm)
| (t =* s) := t.sub_terms <|> s.sub_terms
| (t ≤* s) := t.sub_terms <|> s.sub_terms
| (¬* p)   := p.sub_terms
| (p ∨* q) := p.sub_terms <|> q.sub_terms
| (p ∧* q) := p.sub_terms <|> q.sub_terms

/-- Find (t - s) inside a preform and replace it with variable k -/
@[simp] def sub_subst (x y : preterm) (k : nat) : preform → preform
| (t =* s) := preterm.sub_subst x y k t =* preterm.sub_subst x y k s
| (t ≤* s) := preterm.sub_subst x y k t ≤* preterm.sub_subst x y k s
| (¬* p)   := ¬* p.sub_subst
| (p ∨* q) := p.sub_subst ∨* q.sub_subst
| (p ∧* q) := p.sub_subst ∧* q.sub_subst

end preform

/-- Preform which asserts that the value of variable k is
    the truncated difference between preterms t and s -/
def is_diff (t s : preterm) (k : nat) : preform :=
((t =* (s +* (1 ** k))) ∨* (t ≤* s ∧* ((1 ** k) =* &0)))

lemma holds_is_diff {t s : preterm} {k : nat} {v : nat → nat} :
  v k = t.val v - s.val v → (is_diff t s k).holds v :=
begin
  intro h1,
  simp only [preform.holds, is_diff, if_pos (eq.refl 1),
    preterm.val_add, preterm.val_var, preterm.val_const],
  by_cases h2 : t.val v ≤ s.val v,
  { right, refine ⟨h2,_⟩,
    rw [h1, one_mul, nat.sub_eq_zero_iff_le], exact h2 },
  { left, rw [h1, one_mul, add_comm, nat.sub_add_cancel _],
    rw not_le at h2, apply le_of_lt h2 }
end

/-- Helper function for sub_elim -/
def sub_elim_core (t s : preterm) (k : nat) (p : preform) : preform :=
(preform.sub_subst t s k p) ∧* (is_diff t s k)

/-- Return de Brujin index of fresh variable that does not occur
    in any of the arguments -/
def sub_fresh_index (t s : preterm) (p : preform) : nat :=
max p.fresh_index (max t.fresh_index s.fresh_index)

/-- Return a new preform with all subtractions eliminated -/
def sub_elim (t s : preterm) (p : preform) : preform :=
sub_elim_core t s (sub_fresh_index t s p) p

lemma sub_subst_equiv {k : nat} {x y : preterm} {v : nat → nat} :
  ∀ p : preform, p.fresh_index ≤ k → ((preform.sub_subst x y k p).holds
    (update k (x.val v - y.val v) v) ↔ (p.holds v))
| (t =* s) h1 :=
  begin
    simp only [preform.holds, preform.sub_subst],
    apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (t ≤* s) h1 :=
  begin
    simp only [preform.holds, preform.sub_subst],
    apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (¬* p) h1 :=
  by { apply not_iff_not_of_iff, apply sub_subst_equiv p h1 }
| (p ∨* q) h1 :=
  begin
    simp only [preform.holds, preform.sub_subst],
    apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (p ∧* q) h1 :=
  begin
    simp only [preform.holds, preform.sub_subst],
    apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end

lemma sat_sub_elim {t s : preterm} {p : preform} :
  p.sat → (sub_elim t s p).sat :=
begin
  intro h1, simp only [sub_elim, sub_elim_core],
  cases h1 with v h1,
  refine ⟨update (sub_fresh_index t s p) (t.val v - s.val v) v, _⟩,
  constructor,
  { apply (sub_subst_equiv p _).elim_right h1,
    apply le_max_left },
  { apply holds_is_diff, rw update_eq,
    apply fun_mono_2;
    apply preterm.val_constant; intros x h2;
    rw update_eq_of_ne _ (ne.symm (ne_of_gt _));
    apply lt_of_lt_of_le h2;
    apply le_trans _ (le_max_right _ _),
    apply le_max_left, apply le_max_right }
end

lemma unsat_of_unsat_sub_elim (t s : preterm) (p : preform) :
  (sub_elim t s p).unsat → p.unsat :=
(@not_imp_not _ _ (classical.dec _)).elim_right sat_sub_elim

end nat

end omega
