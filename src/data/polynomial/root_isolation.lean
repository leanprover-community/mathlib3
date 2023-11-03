/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.polynomial.ring_division
import data.polynomial.degree.definitions
import data.real.basic
import topology.algebra.order.intermediate_value
import topology.metric_space.basic
import topology.continuous_function.polynomial
import data.sign

/-!
# Root isolation

Algorithms and theorems for locating the roots of real polynomials.

## TODO

* Descartes' rule of signs
* Sturm's Theorem

-/

open_locale classical

open polynomial multiset

lemma opposite_signs_of_roots_filter_mem_Ioo_empty (a b : ℝ) (hab : a ≤ b) (p : polynomial ℝ)
  (hr : ∀ x ∈ set.Icc a b, p.eval x ≠ 0) :
  ((0 < p.eval a ∧ 0 < p.eval b) ∨ (p.eval a < 0 ∧ p.eval b < 0)) :=
begin
  have ha : p.eval a ≠ 0 := hr a (set.left_mem_Icc.mpr hab),
  have hb : p.eval b ≠ 0 := hr b (set.right_mem_Icc.mpr hab),
  have p_nonzero : p ≠ 0,
  { contrapose! ha,
    rw [ha, eval_zero], },
  have p_continuous : continuous_on (λ x, p.eval x) (set.Icc a b) := p.continuous.continuous_on,
  contrapose! hr,
  simp only [ne.def, multiset.empty_eq_zero],
  rw [eq_zero_iff_forall_not_mem],
  push_neg,
  replace ha := ne.lt_or_lt ha,
  replace hb := ne.lt_or_lt hb,
  -- Casework on sign of evaluations at endpoints.
  rcases ha with ha'|ha'; rcases hb with hb'|hb',
  { replace hr := hr.right ha',
    linarith, },
  { have ivt := intermediate_value_Ioo hab p_continuous,
    have zero_mem_image := set.mem_of_mem_of_subset (set.mem_Ioo.mpr ⟨ha', hb'⟩) ivt,
    simp only [set.mem_Ioo, mem_filter, set.mem_image] at zero_mem_image ⊢,
    rcases zero_mem_image with ⟨x, hx⟩,
    use x,
    rwa [mem_roots p_nonzero, is_root, and.comm], },
  { have ivt := intermediate_value_Ioo' hab p_continuous,
    have zero_mem_image := set.mem_of_mem_of_subset (set.mem_Ioo.mpr ⟨hb', ha'⟩) ivt,
    simp only [set.mem_Ioo, mem_filter, set.mem_image] at zero_mem_image ⊢,
    rcases zero_mem_image with ⟨x, hx⟩,
    use x,
    rwa [mem_roots p_nonzero, is_root, and.comm], },
  { replace hr := hr.left ha',
    linarith, },
end

lemma even_card_roots_filter_mem_Ioo_iff (a b : ℝ) (hab : a ≤ b) (p : polynomial ℝ)
  (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
  even ((p.roots.filter (∈ set.Ioo a b)).card)
    ↔ ((0 < p.eval a ∧ 0 < p.eval b) ∨ (p.eval a < 0 ∧ p.eval b < 0)) :=
begin
  generalize hr : ( p.roots.filter (∈ set.Ioo a b)) = root_set,
  revert hr hb ha p,
  refine multiset.induction_on root_set _ _,
  { -- Base case: Polynomial has no roots in the interval.
    intros p ha hb hr,
    simp only [card_zero, true_iff, even_zero],
    exact opposite_signs_of_roots_filter_mem_Ioo_empty a b hab p ha hb hr, },
  { -- Inductive case: Polynomial has at least one root `root` in the interval.
    intros root root_set' hf p ha hb hr,
    have p_nonzero : p ≠ 0,
    { contrapose! ha,
      rw ha,
      simp only [le_refl, and_self, eval_zero], },
    have in_roots : root ∈ filter (∈ set.Ioo a b) p.roots,
    { rw hr, apply multiset.mem_cons_self, },
    rw mem_filter at in_roots,
    rcases in_roots with ⟨is_root, h_root_range⟩,
    rw [mem_roots p_nonzero, ←dvd_iff_is_root] at is_root,
    -- Divide factor out to get a new polynomial on which to apply the inductive hypothesis.
    rcases is_root with ⟨p', hpp'⟩,
    -- Reexpress everything in terms of new polynomial `p'`.
    rw hpp' at *,
    -- Show `p'` meets the criteria to apply the inductive hypothesis
    have ha' : p'.eval a ≠ 0,
    { clear_except ha,
      contrapose! ha,
      simp [ha], },
    have hb' : p'.eval b ≠ 0,
    { clear_except hb,
      contrapose! hb,
      simp [hb], },
    -- In particular, the root set of `p'` is that of `p` with `root` removed.
    have hr' : filter (∈ set.Ioo a b) p'.roots = root_set',
    { clear_except hr p_nonzero h_root_range,
      rw [roots_mul p_nonzero, filter_add, roots_X_sub_C,
        filter_singleton, if_pos h_root_range, singleton_add,
        cons_inj_right] at hr,
      exact hr, },
    -- Apply the inductive hypothesis to `p'`
    replace hf := hf p' ha' hb' hr',
    rw [card_cons, nat.even_add_one, hf],
    clear_except h_root_range ha' hb',
    replace ha' := ne.lt_or_lt ha',
    replace hb' := ne.lt_or_lt hb',
    rcases h_root_range with ⟨hra, hrb⟩,
    have hra' : ¬ root < a, by linarith [hra],
    have hrb' : ¬ b < root, by linarith [hrb],
    -- Reduce to a case bash on the signs of evaluations of `p'`
    simp_rw [eval_mul, eval_sub, eval_X, eval_C, mul_pos_iff, mul_neg_iff, sub_pos, sub_neg,
      hra, hrb, hra', hrb', false_and, true_and, false_or, or_false] at *,
    tauto! {closer := tactic.linarith tt ff []}, },
end
