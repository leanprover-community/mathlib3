/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import data.polynomial.eval
import ring_theory.polynomial.chebyshev.defs

/-!
# Dickson polynomials

The Dickson polynomials are two families of polynomials indexed by `ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`.
They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `x ^ n`.

## Main declarations

* `polynomial.dickson₁`: the Dickson polynomials of the first kind.
* `polynomial.dickson₂`: the Dickson polynomials of the second kind.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Move the definition of `lambdashev` from `chebyshev.defs` into this file
  (or even remove it because it is a special case of the polynomials defined here?).
* Show that `lambdashev` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
-/

noncomputable theory

namespace polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S] (a : R)

/-- `dickson₁` is the `n`-th Dickson polynomial of the first kind associated to the element `a∈R`.
-/
noncomputable def dickson₁ : ℕ → polynomial R
| 0       := 2
| 1       := X
| (n + 2) := X * dickson₁ (n + 1) - (monomial 0 a) * dickson₁ n

@[simp] lemma dickson₁_zero : dickson₁ a 0 = 2 := rfl
@[simp] lemma dickson₁_one : dickson₁ a 1 = X := rfl
lemma dickson₁_two : dickson₁ a 2 = X ^ 2 - monomial 0 a * 2 :=
by simp only [dickson₁, mul_one, pow_two]
@[simp] lemma dickson₁_add_two (n : ℕ) :
  dickson₁ a (n + 2) = X * dickson₁ a (n + 1) - (monomial 0 a) * dickson₁ a n :=
by rw dickson₁

lemma dickson₁_of_two_le (n : ℕ) (h : 2 ≤ n) :
  dickson₁ a n = X * dickson₁ a (n - 1) - (monomial 0 a) * dickson₁ a (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact dickson₁_add_two R a n
end

variables {R S a}

lemma map_dickson₁ (f : R →+* S) :
  ∀ (n : ℕ), map f (dickson₁ a n) = dickson₁ (f a) n
| 0       := by simp only [dickson₁_zero, bit0, map_add, map_one]
| 1       := by simp only [dickson₁_one, map_X]
| (n + 2) :=
begin
  simp only [dickson₁_add_two, map_sub, map_mul, map_X, map_monomial],
  rw [map_dickson₁ (n + 1), map_dickson₁ n]
end

variable {R}

lemma lambdashev_eq_dickson₁_of_eq_one :
∀ (n : ℕ), lambdashev n = dickson₁ 1 n
| 0       := by simp only [lambdashev_zero, dickson₁_zero]
| 1       := by simp only [lambdashev_one, dickson₁_one]
| (n + 2) :=
begin
  simp only [lambdashev_add_two, dickson₁_add_two],
  rw [lambdashev_eq_dickson₁_of_eq_one, lambdashev_eq_dickson₁_of_eq_one],
  change X * dickson₁ 1 (n + 1) - dickson₁ 1 n = X * dickson₁ 1 (n + 1) - 1 * dickson₁ 1 n,
  rw one_mul
end

variables {R S a}

/-- `dickson₂` is the `n`-th Dickson polynomial of the second kind associated to the element `a∈R`.
-/
noncomputable def dickson₂ : ℕ → polynomial R
| 0       := 1
| 1       := X
| (n + 2) := X * dickson₂ (n + 1) - (monomial 0 a) * dickson₂ n

@[simp] lemma dickson₂_zero : dickson₂ a 0 = 1 := rfl
@[simp] lemma dickson₂_one : dickson₂ a 1 = X := rfl
lemma dickson₂_two : dickson₂ a 2 = X ^ 2 - monomial 0 a :=
by simp only [dickson₂, mul_one, pow_two]
@[simp] lemma dickson₂_add_two (n : ℕ) :
  dickson₂ a (n + 2) = X * dickson₂ a (n + 1) - (monomial 0 a) * dickson₂ a n :=
by rw dickson₂

lemma dickson₂_of_two_le (n : ℕ) (h : 2 ≤ n) :
  dickson₂ a n = X * dickson₂ a (n - 1) - (monomial 0 a) * dickson₂ a (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact dickson₂_add_two a n
end

variables {R S a}

lemma map_dickson₂ (f : R →+* S) :
  ∀ (n : ℕ), map f (dickson₂ a n) = dickson₂ (f a) n
| 0       := by simp only [dickson₂_zero, map_one]
| 1       := by simp only [dickson₂_one, map_X]
| (n + 2) :=
begin
  simp only [dickson₂_add_two, map_sub, map_mul, map_X, map_monomial],
  rw [map_dickson₂ (n + 1), map_dickson₂ n]
end

end polynomial
