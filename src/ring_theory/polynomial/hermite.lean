/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/

import data.polynomial.derivative

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
open polynomial

/-- the nth probabilist's Hermite polynomial -/
noncomputable def hermite : ℕ → polynomial ℤ
| 0     := 1
| (n+1) := X * (hermite n) - (hermite n).derivative

@[simp] lemma hermite_succ {n : ℕ} : hermite (n+1) =  X * (hermite n) - (hermite n).derivative :=
by rw hermite

@[simp] lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp] lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, hermite_zero],
  simp only [map_one, mul_one, derivative_one, sub_zero]
end
