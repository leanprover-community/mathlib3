/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.eval

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.
In this file, we only consider Chebyshev polynomials of the first kind.

See the file `ring_theory.polynomial.chebyshev.basic` for more properties.

## Main declarations

* `polynomial.chebyshev₁`: the Chebyshev polynomials of the first kind.
* `polynomial.lambdashev`: a variant on the Chebyshev polynomials that define a Lambda structure
  on `polynomial ℤ`.

## Implementation details

In this file we only give definitions and some very elementary simp-lemmas.
This way, we can import this file in `analysis.special_functions.trigonometric`,
and import that file in turn, in `ring_theory.polynomial.chebyshev.basic`.

## TODO

Add Chebyshev polynomials of the second kind.
-/


noncomputable theory

namespace polynomial

variables (R S : Type*) [comm_ring R] [comm_ring S]

/-- `chebyshev₁ n` is the `n`-th Chebyshev polynomial of the first kind -/
noncomputable def chebyshev₁ : ℕ → polynomial R
| 0       := 1
| 1       := X
| (n + 2) := 2 * X * chebyshev₁ (n + 1) - chebyshev₁ n

@[simp] lemma chebyshev₁_zero : chebyshev₁ R 0 = 1 := rfl
@[simp] lemma chebyshev₁_one : chebyshev₁ R 1 = X := rfl
lemma chebyshev₁_two : chebyshev₁ R 2 = 2 * X ^ 2 - 1 :=
by simp only [chebyshev₁, sub_left_inj, pow_two, mul_assoc]
@[simp] lemma chebyshev₁_add_two (n : ℕ) :
  chebyshev₁ R (n + 2) = 2 * X * chebyshev₁ R (n + 1) - chebyshev₁ R n :=
by rw chebyshev₁

lemma chebyshev₁_two_le (n : ℕ) (h : 2 ≤ n) :
  chebyshev₁ R n = 2 * X * chebyshev₁ R (n - 1) - chebyshev₁ R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact chebyshev₁_add_two R n
end

variables {R S}

lemma map_chebyshev₁ (f : R →+* S) :
  ∀ (n : ℕ), map f (chebyshev₁ R n) = chebyshev₁ S n
| 0       := by simp only [chebyshev₁_zero, map_one]
| 1       := by simp only [chebyshev₁_one, map_X]
| (n + 2) :=
begin
  simp only [chebyshev₁_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_chebyshev₁ (n + 1), map_chebyshev₁ n],
end

variables (R)

/-- `lambdashev R n` is equal to `2 * (chebyshev₁ R n).comp (X / 2)`.
It is a family of polynomials that satisfies
`lambdashev (zmod p) p = X ^ p`, and therefore defines a Lambda structure on `polynomial ℤ`. -/
noncomputable def lambdashev : ℕ → polynomial R
| 0       := 2
| 1       := X
| (n + 2) := X * lambdashev (n + 1) - lambdashev n

@[simp] lemma lambdashev_zero : lambdashev R 0 = 2 := rfl
@[simp] lemma lambdashev_one : lambdashev R 1 = X := rfl
lemma lambdashev_two : lambdashev R 2 = X ^ 2 - 2 :=
by simp only [lambdashev, sub_left_inj, pow_two, mul_assoc]
@[simp] lemma lambdashev_add_two (n : ℕ) :
  lambdashev R (n + 2) = X * lambdashev R (n + 1) - lambdashev R n :=
by rw lambdashev

lemma lambdashev_two_le (n : ℕ) (h : 2 ≤ n) :
  lambdashev R n = X * lambdashev R (n - 1) - lambdashev R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact lambdashev_add_two R n
end

variables {R S}

lemma map_lambdashev (f : R →+* S) :
  ∀ (n : ℕ), map f (lambdashev R n) = lambdashev S n
| 0       := by simp only [lambdashev_zero, bit0, map_add, map_one]
| 1       := by simp only [lambdashev_one, map_X]
| (n + 2) :=
begin
  simp only [lambdashev_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_lambdashev (n + 1), map_lambdashev n],
end


end polynomial
