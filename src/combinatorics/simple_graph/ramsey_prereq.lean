/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.big_operators.ring_mathlib
import algebra.order.monoid.lemmas_mathlib
import combinatorics.simple_graph.basic_mathlib
import combinatorics.simple_graph.degree_sum_mathlib
import data.nat.choose.basic_mathlib
import data.nat.choose.central_mathlib
import data.nat.choose.sum_mathlib
import data.nat.factorial.basic_mathlib
import data.fin.vec_notation_mathlib

/-!
# Misc prereqs and collect imports
-/

lemma fin.ne_zero_iff_eq_one : ∀ {x : fin 2}, x ≠ 0 ↔ x = 1 := by dec_trivial

lemma fin.eq_zero_iff_ne_one : ∀ {x : fin 2}, x = 0 ↔ x ≠ 1 := by dec_trivial

lemma fin.fin_two_eq_zero_of_ne_one {x : fin 2} (hx : x ≠ 1) : x = 0 :=
by rwa [fin.eq_zero_iff_ne_one]
