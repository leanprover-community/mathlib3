/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import data.polynomial.eval
import ring_theory.polynomial.chebyshev.defs

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `polynomial.dickson`: the generalised Dickson polynomials.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `linear_recurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

noncomputable theory

namespace polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S] (k : ℕ) (a : R)

/-- `dickson` is the `n`the (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → polynomial R
| 0       := 3 - k
| 1       := X
| (n + 2) := X * dickson (n + 1) - (C a) * dickson n

@[simp] lemma dickson_zero : dickson k a 0 = 3 - k := rfl
@[simp] lemma dickson_one : dickson k a 1 = X := rfl
lemma dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k) :=
by simp only [dickson, pow_two]
@[simp] lemma dickson_add_two (n : ℕ) :
  dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n :=
by rw dickson

lemma dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
  dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact dickson_add_two k a n
end

variables {R S k a}

lemma map_dickson (f : R →+* S) :
  ∀ (n : ℕ), map f (dickson k a n) = dickson k (f a) n
| 0       := by simp only [dickson_zero, map_sub, map_nat_cast, bit1, bit0, map_add, map_one]
| 1       := by simp only [dickson_one, map_X]
| (n + 2) :=
begin
  simp only [dickson_add_two, map_sub, map_mul, map_X, map_C],
  rw [map_dickson, map_dickson]
end

variable {R}

@[simp] lemma dickson_two_zero :
  ∀ (n : ℕ), dickson 2 (0 : R) n = X ^ n
| 0       := by { simp only [dickson_zero, pow_zero], norm_num }
| 1       := by simp only [dickson_one, pow_one]
| (n + 2) :=
begin
  simp only [dickson_add_two, C_0, zero_mul, sub_zero],
  rw [dickson_two_zero, pow_add X (n + 1) 1, mul_comm, pow_one]
end

end polynomial
