/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau.
-/

import ring_theory.polynomial

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

-/

universes u v w
open_locale classical

namespace polynomial

section comm_semiring

variables {R : Type u} [comm_semiring R]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable (f : polynomial R) : Prop :=
is_coprime f f.derivative

lemma separable_def (f : polynomial R) :
  f.separable ↔ is_coprime f f.derivative :=
iff.rfl

lemma separable_def' (f : polynomial R) :
  f.separable ↔ ∃ a b : polynomial R, a * f + b * f.derivative = 1 :=
iff.rfl

lemma separable_one : (1 : polynomial R).separable :=
is_coprime_one_left

lemma separable_X_add_C (a : R) : (X + C a).separable :=
by { rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero],
  exact is_coprime_one_right }

lemma separable_X : (X : polynomial R).separable :=
by { rw [separable_def, derivative_X], exact is_coprime_one_right }

lemma separable.of_mul_left {f g : polynomial R} (h : (f * g).separable) : f.separable :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_left (is_coprime.of_add_mul_left_right this)
end

lemma separable.of_mul_right {f g : polynomial R} (h : (f * g).separable) : g.separable :=
by { rw mul_comm at h, exact h.of_mul_left }

end comm_semiring

section comm_ring

variables {R : Type u} [comm_ring R]

lemma separable.mul {f g : polynomial R} (hf : f.separable) (hg : g.separable)
  (h : is_coprime f g) : (f * g).separable :=
by { rw [separable_def, derivative_mul], exact ((hf.mul_right h).add_mul_left_right _).mul_left
  ((h.symm.mul_right hg).mul_add_right_right _) }

end comm_ring

end polynomial
