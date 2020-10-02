/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import tactic
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree

open polynomial finsupp finset

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}

lemma pol_ind_card_degree_bound (N : ℕ) {P : ℕ → polynomial R → Prop}
 (Padd : ∀ f g : polynomial R , ∀ M : ℕ , f.nat_degree ≤ M → g.nat_degree ≤ M → P  M f → P M g → P M (f+g))
 (Pmon : ∀ r : R , ∀ n M : ℕ , n ≤ M → P M (C r * X^n)) :
 ∀ f : polynomial R , ∀ M : ℕ , f.support.card ≤ N.succ → f.nat_degree ≤ M → P M f :=
begin
    induction N with N hN,
    {
      intros f M hf hM,
      rw term_of_card_support_le_one (hf),
      apply Pmon (f.leading_coeff) f.nat_degree M hM,
    },
    { intros f M hf hM,
      rw sum_leading_term_remove f,
      apply Padd,
        apply le_trans _ hM,
        exact nat_degree_remove_leading_coefficient_le,

        apply le_trans _ hM,
        apply nat_degree_term_le,
        apply hN,

        by_cases f0 : f = 0,
        rw [f0, remove_leading_coefficient_zero, polynomial.support_zero, card_empty],
        exact zero_le _,

        rw ← support_remove_leading_coefficient_succ at hf,
        repeat {rw nat.succ_eq_add_one at hf},
        finish,

        intro,
        rw a at hf,
        simp at hf,
        finish,

        { apply le_trans _ hM,
          exact nat_degree_remove_leading_coefficient_le, },

        apply Pmon f.leading_coeff f.nat_degree M hM, },
end


lemma pol_ind_degree_bound {P : ℕ → polynomial R → Prop} {M : ℕ}
 {Padd : ∀ f g : polynomial R , ∀ N : ℕ , f.nat_degree ≤ N → g.nat_degree ≤ N → P N f → P N g → P N (f+g) }
 {Pmon : ∀ r : R , ∀ n N : ℕ , n ≤ N → P N (C r * X^n) } :
 f.nat_degree ≤ M → P M f :=
 begin
  intro,
  by_cases f0 : f = 0,
    { rw f0,
      convert Pmon 0 0 M (nat.zero_le _),
      rw [C_0, zero_mul], },
    { apply pol_ind_card_degree_bound f.support.card.pred Padd Pmon,
      rw [nat.succ_eq_add_one, nat.pred_eq_sub_one],
      rw nat.sub_add_cancel,
      apply xx,
      intro,
      apply f0,
      rw card_eq_zero at a_1,
      rwa ← zero_iff_empty,

      assumption, },
 end


lemma pol_ind_card (N : ℕ) {P : polynomial R → Prop}
 (Padd : ∀ f g : polynomial R , P f → P g → P (f+g))
 (Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)) :
 ∀ f : polynomial R , f.support.card = N.succ → P f :=
begin
  induction N with N hN,
    {
      intros f hf,
      rw term_of_card_support_le_one (le_of_eq hf),
      apply Pmon,
    },
    { intros f hf,
      rw sum_leading_term_remove f,
      apply Padd,
        apply hN,
        rw ← support_remove_leading_coefficient_succ at hf,
        finish,

        intro,
        rw a at hf,
        simp at hf,
        finish,

        apply Pmon, },
end




lemma pol_ind_1 {P : polynomial R → Prop}
 {Padd : ∀ f g : polynomial R , P f → P g → P (f+g) }
 {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n) } :
 P f :=
begin
  by_cases f0 : f = 0,
    { rw f0,
      convert Pmon 0 0,
      rw [C_0, zero_mul], },
    { apply pol_ind_card f.support.card.pred Padd Pmon,
      rw [nat.succ_eq_add_one, nat.pred_eq_sub_one],
      rw nat.sub_add_cancel,
      apply xx,
      intro,
      apply f0,
      rw card_eq_zero at a,
      rwa ← zero_iff_empty, },
end


lemma pol_ind_with_N (N : ℕ) {P : polynomial R → Prop}
 (Psum : ∀ (p q : polynomial R), (P p) → (P q) → (P (p+q)))
 (Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)) :
 ∀ p : polynomial R, p.support.card ≤ N.succ → P p :=
begin
  induction N,
    { intros p hp,
      rw term_of_card_support_le_one hp,
      exact Pmon p.leading_coeff p.nat_degree, },

    { intros p hp,
      by_cases p0 : p = 0,
        { rw [p0, ← zero_mul X, ← C_0, ← pow_one X],
          exact Pmon 0 1, },
        { rw sum_leading_term_remove p,
          apply Psum,
            { apply N_ih,
              apply nat.le_of_lt_succ,
              apply gt_of_ge_of_gt hp _,
              exact support_remove_lt p0, },
            { exact Pmon (leading_coeff p) (nat_degree p), }, }, },
end

lemma pol_ind (f : polynomial R) {P : polynomial R → Prop}
 {Psum : ∀ p q : polynomial R, (P p) → (P q) → (P (p+q))}
 {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)} :
 P f :=
begin
  apply pol_ind_with_N f.support.card Psum Pmon,
  exact f.support.card.le_succ,
end

end polynomial
