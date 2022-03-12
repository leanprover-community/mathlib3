/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.basic
/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`algebra.continued_fractions.basic`.
-/

namespace generalized_continued_fraction

section general
/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/

variables {α : Type*} {g : generalized_continued_fraction α} {n : ℕ}

lemma terminated_at_iff_s_terminated_at : g.terminated_at n ↔ g.s.terminated_at n := by refl

lemma terminated_at_iff_s_none : g.terminated_at n ↔ g.s.nth n = none := by refl

lemma part_num_none_iff_s_none : g.partial_numerators.nth n = none ↔ g.s.nth n = none :=
by cases s_nth_eq : (g.s.nth n); simp [partial_numerators, s_nth_eq]

lemma terminated_at_iff_part_num_none : g.terminated_at n ↔ g.partial_numerators.nth n = none :=
by rw [terminated_at_iff_s_none, part_num_none_iff_s_none]

lemma part_denom_none_iff_s_none : g.partial_denominators.nth n = none ↔ g.s.nth n = none :=
by cases s_nth_eq : (g.s.nth n); simp [partial_denominators, s_nth_eq]

lemma terminated_at_iff_part_denom_none : g.terminated_at n ↔ g.partial_denominators.nth n = none :=
by rw [terminated_at_iff_s_none, part_denom_none_iff_s_none]

lemma part_num_eq_s_a {gp : pair α} (s_nth_eq : g.s.nth n = some gp) :
  g.partial_numerators.nth n = some gp.a :=
by simp [partial_numerators, s_nth_eq]

lemma part_denom_eq_s_b {gp : pair α} (s_nth_eq : g.s.nth n = some gp) :
  g.partial_denominators.nth n = some gp.b :=
by simp [partial_denominators, s_nth_eq]

lemma exists_s_a_of_part_num {a : α} (nth_part_num_eq : g.partial_numerators.nth n = some a) :
  ∃ gp, g.s.nth n = some gp ∧ gp.a = a :=
by simpa [partial_numerators, seq.map_nth] using nth_part_num_eq

lemma exists_s_b_of_part_denom {b : α} (nth_part_denom_eq : g.partial_denominators.nth n = some b) :
  ∃ gp, g.s.nth n = some gp ∧ gp.b = b :=
by simpa [partial_denominators, seq.map_nth] using nth_part_denom_eq

end general

section with_division_ring
/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/

variables {K : Type*} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K]

lemma nth_cont_eq_succ_nth_cont_aux : g.continuants n = g.continuants_aux (n + 1) := rfl
lemma num_eq_conts_a : g.numerators n = (g.continuants n).a := rfl
lemma denom_eq_conts_b : g.denominators n = (g.continuants n).b := rfl
lemma convergent_eq_num_div_denom : g.convergents n = g.numerators n / g.denominators n := rfl
lemma convergent_eq_conts_a_div_conts_b :
  g.convergents n = (g.continuants n).a / (g.continuants n).b := rfl

lemma exists_conts_a_of_num {A : K} (nth_num_eq : g.numerators n = A) :
  ∃ conts, g.continuants n = conts ∧ conts.a = A :=
by simpa

lemma exists_conts_b_of_denom {B : K} (nth_denom_eq : g.denominators n = B) :
  ∃ conts, g.continuants n = conts ∧ conts.b = B :=
by simpa

@[simp]
lemma zeroth_continuant_aux_eq_one_zero : g.continuants_aux 0 = ⟨1, 0⟩ := rfl
@[simp]
lemma first_continuant_aux_eq_h_one : g.continuants_aux 1 = ⟨g.h, 1⟩ := rfl
@[simp]
lemma zeroth_continuant_eq_h_one : g.continuants 0 = ⟨g.h, 1⟩ := rfl
@[simp]
lemma zeroth_numerator_eq_h : g.numerators 0 = g.h := rfl
@[simp]
lemma zeroth_denominator_eq_one : g.denominators 0 = 1 := rfl
@[simp]
lemma zeroth_convergent_eq_h : g.convergents 0 = g.h :=
by simp [convergent_eq_num_div_denom, num_eq_conts_a, denom_eq_conts_b, div_one]

lemma second_continuant_aux_eq {gp : pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
  g.continuants_aux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ :=
by simp [zeroth_s_eq, continuants_aux, next_continuants, next_denominator, next_numerator]

lemma first_continuant_eq {gp : pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
  g.continuants 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ :=
by simp [nth_cont_eq_succ_nth_cont_aux, (second_continuant_aux_eq zeroth_s_eq)]

lemma first_numerator_eq {gp : pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
  g.numerators 1 = gp.b * g.h + gp.a :=
by simp[num_eq_conts_a, (first_continuant_eq zeroth_s_eq)]

lemma first_denominator_eq {gp : pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
  g.denominators 1 = gp.b :=
by simp[denom_eq_conts_b, (first_continuant_eq zeroth_s_eq)]

@[simp]
lemma zeroth_convergent'_aux_eq_zero {s : seq $ pair K} : convergents'_aux s 0 = 0 := rfl
@[simp]
lemma zeroth_convergent'_eq_h : g.convergents' 0 = g.h := by simp [convergents']

end with_division_ring
end generalized_continued_fraction
