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
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

namespace generalized_continued_fraction

variables {K : Type*} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K]

lemma continuants_aux_recurrence
  {gp ppred pred : pair K} (nth_s_eq : g.s.nth n = some gp)
  (nth_conts_aux_eq : g.continuants_aux n = ppred)
  (succ_nth_conts_aux_eq : g.continuants_aux (n + 1) = pred) :
  g.continuants_aux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
by { substs pred ppred, simp only [*, continuants_aux], refl }

lemma continuants_recurrence_aux
  {gp ppred pred : pair K} (nth_s_eq : g.s.nth n = some gp)
  (nth_conts_aux_eq : g.continuants_aux n = ppred)
  (succ_nth_conts_aux_eq : g.continuants_aux (n + 1) = pred) :
  g.continuants.nth (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
continuants_aux_recurrence nth_s_eq nth_conts_aux_eq succ_nth_conts_aux_eq

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem continuants_recurrence
  {gp ppred pred : pair K}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_conts_eq : g.continuants.nth n = ppred)
  (succ_nth_conts_eq : g.continuants.nth (n + 1) = pred) :
  g.continuants.nth (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
continuants_recurrence_aux succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
lemma numerators_recurrence {gp : pair K} {ppredA predA : K}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_num_eq : g.numerators.nth n = ppredA)
  (succ_nth_num_eq : g.numerators.nth (n + 1) = predA) :
  g.numerators.nth (n + 2) = gp.b * predA + gp.a * ppredA :=
begin
  obtain ⟨ppredConts, nth_conts_eq, rfl⟩ : ∃ conts, g.continuants.nth n = conts ∧ conts.a = ppredA,
    from exists_conts_a_of_num nth_num_eq,
  obtain ⟨predConts, succ_nth_conts_eq, rfl⟩ :
    ∃ conts, g.continuants.nth (n + 1) = conts ∧ conts.a = predA,
    from exists_conts_a_of_num succ_nth_num_eq,
  rw [num_eq_conts_a, (continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq)]
end

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
lemma denominators_recurrence {gp : pair K} {ppredB predB : K}
  (succ_nth_s_eq : g.s.nth (n + 1) = some gp)
  (nth_denom_eq : g.denominators.nth n = ppredB)
  (succ_nth_denom_eq : g.denominators.nth (n + 1) = predB) :
  g.denominators.nth (n + 2) = gp.b * predB + gp.a * ppredB :=
begin
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.continuants.nth n = conts ∧ conts.b = ppredB,
    from exists_conts_b_of_denom nth_denom_eq,
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
    ∃ conts, g.continuants.nth (n + 1) = conts ∧ conts.b = predB,
    from exists_conts_b_of_denom succ_nth_denom_eq,
  rw [denom_eq_conts_b, (continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq)]
end

end generalized_continued_fraction
