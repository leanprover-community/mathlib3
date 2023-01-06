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

lemma terminated_at_iff_s_terminated_at : g.terminated_at n ↔ g.s.terminated_at n := iff.rfl

lemma terminated_at_iff_s_none : g.terminated_at n ↔ g.s.nth n = none := iff.rfl

lemma part_num_none_iff_s_none : g.partial_numerators.nth n = none ↔ g.s.nth n = none :=
option.map_eq_none'

lemma terminated_at_iff_part_num_none : g.terminated_at n ↔ g.partial_numerators.nth n = none :=
seq.terminated_at_map.symm

lemma part_denom_none_iff_s_none : g.partial_denominators.nth n = none ↔ g.s.nth n = none :=
option.map_eq_none'

lemma terminated_at_iff_part_denom_none : g.terminated_at n ↔ g.partial_denominators.nth n = none :=
seq.terminated_at_map.symm

lemma part_num_eq_s_a {gp : pair α} (s_nth_eq : g.s.nth n = some gp) :
  g.partial_numerators.nth n = some gp.a :=
option.map_eq_some'.2 ⟨_, s_nth_eq, rfl⟩

lemma part_denom_eq_s_b {gp : pair α} (s_nth_eq : g.s.nth n = some gp) :
  g.partial_denominators.nth n = some gp.b :=
option.map_eq_some'.2 ⟨_, s_nth_eq, rfl⟩

lemma exists_s_a_of_part_num {a : α} (nth_part_num_eq : g.partial_numerators.nth n = some a) :
  ∃ gp, g.s.nth n = some gp ∧ gp.a = a :=
option.map_eq_some'.1 nth_part_num_eq

lemma exists_s_b_of_part_denom {b : α} (nth_part_denom_eq : g.partial_denominators.nth n = some b) :
  ∃ gp, g.s.nth n = some gp ∧ gp.b = b :=
option.map_eq_some'.1 nth_part_denom_eq

end general

section with_division_ring
/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/

variables {K : Type*} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K]

lemma nth_continuants : g.continuants.nth n = g.continuants_aux (n + 1) := rfl
lemma num_eq_conts_a : g.numerators.nth n = (g.continuants.nth n).a := rfl
lemma denom_eq_conts_b : g.denominators.nth n = (g.continuants.nth n).b := rfl
lemma convergent_eq_num_div_denom : g.convergents.nth n = g.numerators.nth n / g.denominators.nth n := rfl
lemma convergent_eq_conts_a_div_conts_b :
  g.convergents.nth n = (g.continuants.nth n).a / (g.continuants.nth n).b := rfl

lemma exists_conts_a_of_num {A : K} (nth_num_eq : g.numerators.nth n = A) :
  ∃ conts, g.continuants.nth n = conts ∧ conts.a = A :=
by simpa

lemma exists_conts_b_of_denom {B : K} (nth_denom_eq : g.denominators.nth n = B) :
  ∃ conts, g.continuants.nth n = conts ∧ conts.b = B :=
by simpa

@[simp] lemma continuant_aux_zero : g.continuants_aux 0 = ⟨1, 0⟩ := rfl
@[simp] lemma continuant_aux_one : g.continuants_aux 1 = ⟨g.h, 1⟩ := rfl
@[simp] lemma head_continuant_eq_h_one : g.continuants.head = ⟨g.h, 1⟩ := rfl
@[simp] lemma head_numerator_eq_h : g.numerators.head = g.h := rfl
@[simp] lemma head_denominator_eq_one : g.denominators.head = 1 := rfl
@[simp] lemma head_convergent_eq_h : g.convergents.head = g.h := div_one _

lemma continuant_aux_two {gp : pair K} (head_s_eq : g.s.head = some gp) :
  g.continuants_aux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ :=
begin
  simp only [head_s_eq, continuants_aux, next_continuants, next_denominator,
    next_numerator, seq.nth_zero, option.elim, mul_one, mul_zero, add_zero],
  exact ⟨rfl, rfl⟩
end

lemma first_continuant_eq {gp : pair K} (head_s_eq : g.s.head = some gp) :
  g.continuants.nth 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ :=
by simp [nth_continuants, continuant_aux_two head_s_eq]

lemma first_numerator_eq {gp : pair K} (head_s_eq : g.s.head = some gp) :
  g.numerators.nth 1 = gp.b * g.h + gp.a :=
by simp [num_eq_conts_a, first_continuant_eq head_s_eq]

lemma first_denominator_eq {gp : pair K} (head_s_eq : g.s.head = some gp) :
  g.denominators.nth 1 = gp.b :=
by simp [denom_eq_conts_b, first_continuant_eq head_s_eq]

@[simp] lemma zeroth_convergent'_aux_eq_zero {s : seq $ pair K} : convergents'_aux s 0 = 0 := rfl
@[simp] lemma zeroth_convergent'_eq_h : g.convergents' 0 = g.h := by simp [convergents']

end with_division_ring
end generalized_continued_fraction
