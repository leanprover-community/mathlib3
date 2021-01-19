/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.derivative

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

See the file `ring_theory.polynomial.chebyshev.basic` for more properties.

## Main declarations

* `polynomial.chebyshev₁`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev₂`: the Chebyshev polynomials of the second kind.
* `polynomial.lambdashev`: a variant on the Chebyshev polynomials that define a Lambda structure
  on `polynomial ℤ`.
* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.

## Implementation details

In this file we only give definitions and some very elementary simp-lemmas.
This way, we can import this file in `analysis.special_functions.trigonometric`,
and import that file in turn, in `ring_theory.polynomial.chebyshev.basic`.

## TODO

* Add explicit formula involving square roots for chebyshev polynomials
  `ring_theory.polynomial.chebyshev.basic`.
* compute zeroes and extrema of chebyshev polynomials
* prove that the roots of the chebyshev polynomials (except 0) are irrational
* prove minimax properties of chebyshev polynomials
* define a variant of chebyshev polynomials of the second kind removing the 2
  (sometimes Dickson polynomials of the second kind) or even more general Dickson polynomials
* prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the matrix zeroes
  of these polynomials
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

lemma chebyshev₁_of_two_le (n : ℕ) (h : 2 ≤ n) :
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

lemma lambdashev_eq_two_le (n : ℕ) (h : 2 ≤ n) :
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

namespace polynomial

variables (R S : Type*) [comm_ring R] [comm_ring S]

/-- `chebyshev₂ n` is the `n`-th Chebyshev polynomial of the second kind -/
noncomputable def chebyshev₂ : ℕ → polynomial R
| 0       := 1
| 1       := 2 * X
| (n + 2) := 2 * X * chebyshev₂ (n + 1) - chebyshev₂ n

@[simp] lemma chebyshev₂_zero : chebyshev₂ R 0 = 1 := rfl
@[simp] lemma chebyshev₂_one : chebyshev₂ R 1 = 2 * X := rfl
lemma chebyshev₂_two : chebyshev₂ R 2 = 4 * X ^ 2 - 1 :=
begin
  simp only [chebyshev₂, sub_left_inj],
  rw [←mul_assoc, mul_comm 2 X, ←mul_comm, mul_assoc, ←mul_assoc, mul_comm (X * X), pow_two],
  norm_num,
end

@[simp] lemma chebyshev₂_add_two (n : ℕ) :
  chebyshev₂ R (n + 2) = 2 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n :=
by rw chebyshev₂

lemma chebyshev₂_of_two_le (n : ℕ) (h : 2 ≤ n) :
  chebyshev₂ R n = 2 * X * chebyshev₂ R (n - 1) - chebyshev₂ R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact chebyshev₂_add_two R n
end

lemma chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ :
∀ (n : ℕ), chebyshev₂ R (n+1) = X * chebyshev₂ R n + chebyshev₁ R (n+1)
|0        := by simp only [chebyshev₂_zero, chebyshev₂_one, chebyshev₁_one, two_mul, mul_one]
|1        := by simpa only [chebyshev₂_one, chebyshev₁_two, chebyshev₂_two, ←mul_assoc, pow_two,
                            mul_comm, add_sub, ←mul_add]
|(n + 2)  := begin
  calc chebyshev₂ R (n + 2 + 1) = 2 * X * chebyshev₂ R (n + 1 + 1) - chebyshev₂ R (n + 1)
                : by rw chebyshev₂_add_two
  ... = 2 * X * (X * chebyshev₂ R (n + 1) + chebyshev₁ R (n + 2))
                                          - (X * chebyshev₂ R n + chebyshev₁ R (n+1))
                : by simp only [chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ n,
                                chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ (n+1)]
  ... = (2 * X * (X * chebyshev₂ R (n + 1)) + 2 * X * chebyshev₁ R (n+2))
                                            - X * chebyshev₂ R n - chebyshev₁ R (n+1)
                : by rw [mul_add, sub_add_eq_sub_sub]
  ... = (2 * X * (X * chebyshev₂ R (n + 1))) - X * chebyshev₂ R n + 2 * X * chebyshev₁ R (n+2)
                                                                  - chebyshev₁ R (n+1)
                : by simp only [sub_add_eq_add_sub]
  ... =  X * (2 * (X * chebyshev₂ R (n + 1)) - chebyshev₂ R n) + (2 * X * chebyshev₁ R (n + 1 + 1)
                                                               - chebyshev₁ R (n + 1))
                : by simp only [add_sub_assoc, mul_comm, mul_assoc, mul_sub]
  ... = X * chebyshev₂ R (n + 2) + chebyshev₁ R (n + 2 + 1)
                : by simp only [mul_assoc, chebyshev₂_add_two, chebyshev₁_add_two]
end

lemma chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂ :
∀ (n : ℕ), chebyshev₁ R (n+1) = chebyshev₂ R (n+1) - X * chebyshev₂ R n :=
begin
  intro n,
  calc chebyshev₁ R (n+1) = chebyshev₁ R (n+1) + X * chebyshev₂ R n - X * chebyshev₂ R n
                                      : by rw add_sub_cancel
  ...                     = X * chebyshev₂ R n + chebyshev₁ R (n+1) - X * chebyshev₂ R n
                                      : by rw add_comm
  ...                     = chebyshev₂ R (n+1) - X * chebyshev₂ R n
                                      : by rw chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁
end

lemma chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂ :
∀ (n : ℕ), chebyshev₁ R (n+2) = X * chebyshev₁ R (n+1) - (1 - X ^ 2) * chebyshev₂ R n
|0        := by simp only [chebyshev₁_one, chebyshev₁_two, chebyshev₂_zero, mul_one,
                 sub_sub_assoc_swap, pow_two, two_mul]
|1        := begin simp only [chebyshev₁_add_two, chebyshev₁_zero, chebyshev₁_add_two,
                              chebyshev₂_one, chebyshev₁_one, sub_mul, mul_sub, mul_one, one_mul],
                              sorry end
|(n + 2)  := begin
calc chebyshev₁ R (n + 2 + 2) = 2 * X * chebyshev₁ R (n + 2 + 1) - chebyshev₁ R (n + 2)
                                : chebyshev₁_add_two _ _
... = 2 * X * (X * chebyshev₁ R (n + 2) - (1 - X ^ 2) * chebyshev₂ R (n + 1))
                                        - (X * chebyshev₁ R (n + 1) - (1 - X ^ 2) * chebyshev₂ R n)
                                : by simp only [chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂]
... = 2 * X * (X * chebyshev₁ R (n + 2)) - 2 * X * ((1 - X ^ 2) * chebyshev₂ R (n + 1))
                                         - X * chebyshev₁ R (n + 1) + (1 - X ^ 2) * chebyshev₂ R n
                                : by rw [mul_sub, sub_add]
... = X * (2 * X * chebyshev₁ R (n + 2) - chebyshev₁ R (n + 1))
                                    - (1 - X ^ 2) * (2 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n)
                                : by sorry
... = X * chebyshev₁ R (n + 2 + 1) - (1 - X ^ 2) * chebyshev₂ R (n + 2)
                                : by simp only [chebyshev₁_add_two, chebyshev₂_add_two]
 end

variables {R S}

lemma map_chebyshev₂ (f : R →+* S) :
  ∀ (n : ℕ), map f (chebyshev₂ R n) = chebyshev₂ S n
| 0       := by simp only [chebyshev₂_zero, map_one]
| 1       := begin simp only [chebyshev₂_one, map_X, map_mul, map_add, map_one],
                   change map f (1+1) * X = 2 * X,
                   simp only [map_add, map_one],
                   refl end
| (n + 2) :=
begin
  simp only [chebyshev₂_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_chebyshev₂ (n + 1), map_chebyshev₂ n],
end

lemma chebyshev₂_derivative_eq_chebyshev₁ :
∀ (n : ℕ), derivative (chebyshev₁ R (n + 1)) = (n + 1) * chebyshev₂ R n
|0        := by simp only [chebyshev₁_one, chebyshev₂_zero, derivative_X, nat.cast_zero, zero_add,
                           mul_one]
|1        := begin  simp only [chebyshev₁_two, chebyshev₂_one, derivative_sub, derivative_one,
                              derivative_mul, derivative_X_pow, sub_zero, nat.cast_one,
                              nat.cast_two],
                    norm_num end
|(n + 2)  := begin rw [chebyshev₁_add_two, derivative_sub, chebyshev₂_derivative_eq_chebyshev₁,
                       derivative_mul, chebyshev₂_derivative_eq_chebyshev₁, derivative_mul,
                       derivative_X, derivative_bit0, derivative_one, bit0_zero, zero_mul,
                       zero_add, mul_one, add_mul, mul_add, one_mul, add_comm, add_assoc,
                       mul_assoc 2 X (chebyshev₂ R (n + 1)), ←mul_add,
                       ←chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁, ←sub_add_eq_add_sub,
                       ←mul_assoc, mul_comm (2 * X)],
                    push_cast,
                    rw [mul_assoc, ←mul_sub, ←chebyshev₂_add_two, ←add_mul],
                    norm_cast,
              end

end polynomial
