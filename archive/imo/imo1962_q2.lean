/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.complex.exponential
import data.polynomial.basic
import data.real.pi

open real

notation `π` := real.pi

/-!
Solve the equation `(cos x)^2 + (cos 2*x)^2 + (cos 3*x)^2 = 1`.

Since Lean does not have a concept of "simplest form", we just express what is
in fact the simplest form of the set of solutions, and then prove it equals the set of solutions.
-/

def problem_equation (x : ℝ) : Prop := (cos x)^2 + (cos 2*x)^2 + (cos 3*x)^2 = 1

def solution_set : set ℝ :=
{ x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 2 ∨ x = (2 * ↑k + 1) * π / 4 ∨
                   x = (6 * ↑k + 1) * π / 6 ∨ x = (6 * ↑k + 5) * π / 6 }

/-
First, we can simplify the left hand side of the problem_equation by writing it in terms
of `(cos x)^2`.
-/

lemma cosx2 (x : ℝ) : (cos x) ^ 2 = 1 - (sin x) ^ 2 :=
begin
  have h1 : (sin x)^2 = 1 - (cos x)^2, from real.sin_square x,
  rw h1,
  ring
end

lemma cos3x (x : ℝ) : cos (3 * x) = 4 * (cos x) ^ 3 - 3 * cos x :=
begin
  have h1 : cos (x + 2 * x) = (cos x) * cos (2 * x) - (sin x) * sin (2 * x),
    from real.cos_add x (2 * x),
  have h2 : x + 2 * x = 3 * x, by ring,
  rw ← h2,
  rw h1,
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, pow_two],
  have h3 : 4 * cos x ^ 3 = 2 * (cos x) * (cos x) * (cos x) + 2 * (cos x) * (cos x)^2, by ring,
  rw [h3, cosx2],
  ring
end

lemma cos2_equiv (x : ℝ) :
cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 =
16 * (cos x ^ 2) ^ 3 - 20 * (cos x ^ 2) ^ 2 + 6 * (cos x ^ 2) + 1 :=
begin
  simp [real.cos_two_mul, cos3x],
  ring
end

def four : polynomial ℝ := (4 : polynomial ℝ)
