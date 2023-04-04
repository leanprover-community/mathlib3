/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/

import data.polynomial.derivative
open polynomial

/-!
# Hermite polynomials

This file defines `hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `x_sub_dx`  : the operation `(x - d/dx)` used to recursively define the Hermite polynomials
* `hermite n` : the nth probabilist's Hermite polynomial, defined as a `polynomial ℤ`, using
                `x_sub_dx` recursively

## References

[Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory

section x_sub_dx

variables {R : Type} [comm_ring R] (p : polynomial R)

/-- the operation `(x - d/dx)` defined for `polynomial R` -/
def x_sub_dx := X * p - p.derivative

@[simp] lemma x_sub_dx_def : x_sub_dx p = X * p - p.derivative := rfl

lemma x_sub_dx_apply {x : R} :
  eval x (x_sub_dx p) = x * (eval x p) - (eval x (derivative p)) := by simp

@[simp] lemma x_sub_dx_map {S : Type} [comm_ring S] {f : R →+* S} :
  x_sub_dx (map f p) = map f (x_sub_dx p) := by simp

end x_sub_dx

section hermite

/-- the nth probabilist's Hermite polynomial -/
def hermite (n : ℕ) : polynomial ℤ := nat.iterate x_sub_dx n 1

lemma hermite_eq_iter {n : ℕ} : hermite n = nat.iterate x_sub_dx n 1 := rfl

@[simp] lemma hermite_succ {n : ℕ} : hermite n.succ = x_sub_dx (hermite n) :=
begin
  rw [hermite_eq_iter, function.iterate_succ' x_sub_dx n],
  refl,
end

@[simp] lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp] lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, x_sub_dx_def, hermite_zero],
  simp only [map_one, mul_one, derivative_one, sub_zero],
end

end hermite
