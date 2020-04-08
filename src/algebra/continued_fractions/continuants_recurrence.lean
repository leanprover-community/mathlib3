/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.translations
/-!
# Recurrence Lemmas for the `continuants` Function of Continued Fractions.

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the `continuants`
function indeed satisfies the following recurrences:

  `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf
variables {α : Type*} {g : gcf α} {n : ℕ} [division_ring α]

lemma continuants_aux_recurrence {gp ppred pred : gcf.pair α} (nth_s_eq : g.s.nth n = some gp)
  (nth_conts_aux_eq : g.continuants_aux n = ppred)
  (succ_nth_conts_aux_eq : g.continuants_aux (n + 1) = pred) :
  g.continuants_aux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
by simp [*, continuants_aux, next_continuants, next_denominator, next_numerator]

lemma continuants_recurrence_aux {gp ppred pred : gcf.pair α} (nth_s_eq : g.s.nth n = some gp)
  (nth_conts_aux_eq : g.continuants_aux n = ppred)
  (succ_nth_conts_aux_eq : g.continuants_aux (n + 1) = pred) :
  g.continuants (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
by simp [nth_cont_eq_succ_nth_cont_aux,
  (continuants_aux_recurrence nth_s_eq nth_conts_aux_eq succ_nth_conts_aux_eq)]

theorem continuants_recurrence {gp ppred pred : gcf.pair α}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_conts_eq : g.continuants n = ppred)
  (succ_nth_conts_eq : g.continuants (n + 1) = pred) :
  g.continuants (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
begin
  rw [nth_cont_eq_succ_nth_cont_aux] at nth_conts_eq succ_nth_conts_eq,
  exact (continuants_recurrence_aux succ_nth_s_eq nth_conts_eq succ_nth_conts_eq)
end

lemma numerators_recurrence {gp : gcf.pair α} {ppredA predA : α}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_num_eq : g.numerators n = ppredA)
  (succ_nth_num_eq : g.numerators (n + 1) = predA) :
  g.numerators (n + 2) = gp.b * predA + gp.a * ppredA :=
begin
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.continuants n = conts ∧ conts.a = ppredA,
    from obtain_conts_a_of_num nth_num_eq,
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
    ∃ conts, g.continuants (n + 1) = conts ∧ conts.a = predA, from
      obtain_conts_a_of_num succ_nth_num_eq,
  rw [num_eq_conts_a, (continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq)]
end

lemma denominators_recurrence {gp : gcf.pair α} {ppredB predB : α}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_denom_eq : g.denominators n = ppredB)
  (succ_nth_denom_eq : g.denominators (n + 1) = predB) :
  g.denominators (n + 2) = gp.b * predB + gp.a * ppredB :=
begin
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.continuants n = conts ∧ conts.b = ppredB,
    from obtain_conts_b_of_denom nth_denom_eq,
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
    ∃ conts, g.continuants (n + 1) = conts ∧ conts.b = predB, from
      obtain_conts_b_of_denom succ_nth_denom_eq,
  rw [denom_eq_conts_b, (continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq)]
end

end generalized_continued_fraction
