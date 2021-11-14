/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth
-/
import data.polynomial.derivative
import tactic.ring

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

## Main definitions

* `polynomial.chebyshev.T`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev.U`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `polynomial.chebyshev.mul_T`, the product of the `m`-th and `(m + k)`-th Chebyshev polynomials of
  the first kind is the sum of the `(2 * m + k)`-th and `k`-th Chebyshev polynomials of the first
  kind.
* `polynomial.chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (int.cast_ring_hom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `linear_recurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/

noncomputable theory
namespace polynomial.chebyshev

open polynomial

variables (R S : Type*) [comm_ring R] [comm_ring S]

/-- `T n` is the `n`-th Chebyshev polynomial of the first kind -/
noncomputable def T : ℕ → polynomial R
| 0       := 1
| 1       := X
| (n + 2) := 2 * X * T (n + 1) - T n

@[simp] lemma T_zero : T R 0 = 1 := rfl
@[simp] lemma T_one : T R 1 = X := rfl
lemma T_two : T R 2 = 2 * X ^ 2 - 1 :=
by simp only [T, sub_left_inj, sq, mul_assoc]
@[simp] lemma T_add_two (n : ℕ) :
  T R (n + 2) = 2 * X * T R (n + 1) - T R n :=
by rw T

lemma T_of_two_le (n : ℕ) (h : 2 ≤ n) :
  T R n = 2 * X * T R (n - 1) - T R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact T_add_two R n
end

variables {R S}

lemma map_T (f : R →+* S) :
  ∀ (n : ℕ), map f (T R n) = T S n
| 0       := by simp only [T_zero, map_one]
| 1       := by simp only [T_one, map_X]
| (n + 2) :=
begin
  simp only [T_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_T (n + 1), map_T n],
end

variables (R S)

/-- `U n` is the `n`-th Chebyshev polynomial of the second kind -/
noncomputable def U : ℕ → polynomial R
| 0       := 1
| 1       := 2 * X
| (n + 2) := 2 * X * U (n + 1) - U n

@[simp] lemma U_zero : U R 0 = 1 := rfl
@[simp] lemma U_one : U R 1 = 2 * X := rfl
lemma U_two : U R 2 = 4 * X ^ 2 - 1 :=
by { simp only [U], ring, }

@[simp] lemma U_add_two (n : ℕ) :
  U R (n + 2) = 2 * X * U R (n + 1) - U R n :=
by rw U

lemma U_of_two_le (n : ℕ) (h : 2 ≤ n) :
  U R n = 2 * X * U R (n - 1) - U R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact U_add_two R n
end

lemma U_eq_X_mul_U_add_T :
  ∀ (n : ℕ), U R (n+1) = X * U R n + T R (n+1)
| 0        := by { simp only [U_zero, U_one, T_one], ring }
| 1        := by { simp only [U_one, T_two, U_two], ring }
| (n + 2)  :=
  calc U R (n + 2 + 1) = 2 * X * (X * U R (n + 1) + T R (n + 2)) - (X * U R n + T R (n + 1)) :
            by simp only [U_add_two, U_eq_X_mul_U_add_T n, U_eq_X_mul_U_add_T (n + 1)]
  ... = X * (2 * X * U R (n + 1) - U R n) + (2 * X * T R (n + 2) - T R (n + 1)) : by ring
  ... = X * U R (n + 2) + T R (n + 2 + 1) : by simp only [U_add_two, T_add_two]

lemma T_eq_U_sub_X_mul_U (n : ℕ) :
  T R (n+1) = U R (n+1) - X * U R n :=
by rw [U_eq_X_mul_U_add_T, add_comm (X * U R n), add_sub_cancel]


lemma T_eq_X_mul_T_sub_pol_U :
  ∀ (n : ℕ), T R (n+2) = X * T R (n+1) - (1 - X ^ 2) * U R n
| 0        := by { simp only [T_one, T_two, U_zero], ring }
| 1        := by { simp only [T_add_two, T_zero, T_add_two,
                              U_one, T_one], ring }
| (n + 2)  :=
calc T R (n + 2 + 2)
    = 2 * X * T R (n + 2 + 1) - T R (n + 2) : T_add_two _ _
... = 2 * X * (X * T R (n + 2) - (1 - X ^ 2) * U R (n + 1))
      - (X * T R (n + 1) - (1 - X ^ 2) * U R n) : by simp only [T_eq_X_mul_T_sub_pol_U]
... = X * (2 * X * T R (n + 2) -  T R (n + 1)) - (1 - X ^ 2) * (2 * X * U R (n + 1) - U R n) :
            by ring
... = X * T R (n + 2 + 1) - (1 - X ^ 2) * U R (n + 2) : by rw [T_add_two _ (n + 1), U_add_two]

lemma one_sub_X_sq_mul_U_eq_pol_in_T (n : ℕ) :
  (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2) :=
by rw [T_eq_X_mul_T_sub_pol_U, ←sub_add, sub_self, zero_add]

variables {R S}

@[simp] lemma map_U (f : R →+* S) :
  ∀ (n : ℕ), map f (U R n) = U S n
| 0       := by simp only [U_zero, map_one]
| 1       :=
begin
  simp only [U_one, map_X, map_mul, map_add, map_one],
  change map f (1+1) * X = 2 * X,
  simpa only [map_add, map_one]
end
| (n + 2) :=
begin
  simp only [U_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_U (n + 1), map_U n],
end

lemma T_derivative_eq_U :
  ∀ (n : ℕ), derivative (T R (n + 1)) = (n + 1) * U R n
| 0        := by simp only [T_one, U_zero, derivative_X, nat.cast_zero, zero_add, mul_one]
| 1        := by { simp only [T_two, U_one, derivative_sub, derivative_one, derivative_mul,
                              derivative_X_pow, nat.cast_one, nat.cast_two],
                    norm_num }
| (n + 2)  :=
  calc derivative (T R (n + 2 + 1))
      = 2 * T R (n + 2) + 2 * X * derivative (T R (n + 1 + 1)) - derivative (T R (n + 1)) :
              by simp only [T_add_two _ (n + 1), derivative_sub, derivative_mul, derivative_X,
                            derivative_bit0, derivative_one, bit0_zero, zero_mul, zero_add, mul_one]
  ... = 2 * (U R (n + 1 + 1) - X * U R (n + 1)) + 2 * X * ((n + 1 + 1) * U R (n + 1))
        - (n + 1) * U R n : by rw_mod_cast [T_derivative_eq_U, T_derivative_eq_U,
                                            T_eq_U_sub_X_mul_U]
  ... = (n + 1) * (2 * X * U R (n + 1) - U R n) + 2 * U R (n + 2) : by ring
  ... = (n + 1) * U R (n + 2) + 2 * U R (n + 2) : by rw U_add_two
  ... = (n + 2 + 1) * U R (n + 2) : by ring
  ... = (↑(n + 2) + 1) * U R (n + 2) : by norm_cast

lemma one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : ℕ) :
  (1 - X ^ 2)  * (derivative (T R (n+1))) =
    (n + 1) * (T R n - X * T R (n+1)) :=
  calc
  (1 - X ^ 2)  * (derivative (T R (n+1))) = (1 - X ^ 2 ) * ((n + 1) * U R n) :
            by rw T_derivative_eq_U
  ... = (n + 1) * ((1 - X ^ 2) * U R n) : by ring
  ... = (n + 1) * (X * T R (n + 1) - (2 * X * T R (n + 1) - T R n)) :
            by rw [one_sub_X_sq_mul_U_eq_pol_in_T, T_add_two]
  ... = (n + 1) * (T R n - X * T R (n+1)) : by ring

lemma add_one_mul_T_eq_poly_in_U (n : ℕ) :
  ((n : polynomial R) + 1) * T R (n+1) =
    X * U R n - (1 - X ^ 2) * derivative ( U R n) :=
begin
  have h : derivative (T R (n + 2)) = (U R (n + 1) - X * U R n) + X * derivative (T R (n + 1))
                                      + 2 * X * U R n - (1 - X ^ 2) * derivative (U R n),
  { conv_lhs { rw T_eq_X_mul_T_sub_pol_U },
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
  one_mul, T_derivative_eq_U],
  rw [T_eq_U_sub_X_mul_U, nat.cast_bit0, nat.cast_one],
  ring },
  calc ((n : polynomial R) + 1) * T R (n + 1)
      = ((n : polynomial R) + 1 + 1) * (X * U R n + T R (n + 1))
        - X * ((n + 1) * U R n) - (X * U R n + T R (n + 1)) : by ring
  ... = derivative (T R (n + 2)) - X * derivative (T R (n + 1)) - U R (n + 1) :
            by rw [←U_eq_X_mul_U_add_T, ←T_derivative_eq_U, ←nat.cast_one, ←nat.cast_add,
                  nat.cast_one, ←T_derivative_eq_U (n + 1)]
  ... = (U R (n + 1) - X * U R n) + X * derivative (T R (n + 1))
        + 2 * X * U R n - (1 - X ^ 2) * derivative (U R n)
        - X * derivative (T R (n + 1)) - U R (n + 1) : by rw h
  ... = X * U R n - (1 - X ^ 2) * derivative (U R n) : by ring,
end

variables (R)

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
lemma mul_T :
  ∀ m : ℕ, ∀ k,
  2 * T R m * T R (m + k) = T R (2 * m + k) + T R k
| 0 := by simp [two_mul, add_mul]
| 1 := by simp [add_comm]
| (m + 2) := begin
  intros k,
  -- clean up the `T` nat indices in the goal
  suffices : 2 * T R (m + 2) * T R (m + k + 2) = T R (2 * m + k + 4) + T R k,
  { have h_nat₁ : 2 * (m + 2) + k = 2 * m + k + 4 := by ring,
    have h_nat₂ : m + 2 + k = m + k + 2 := by simp [add_comm, add_assoc],
    simpa [h_nat₁, h_nat₂] using this },
  -- clean up the `T` nat indices in the inductive hypothesis applied to `m + 1` and
  -- `k + 1`
  have H₁ : 2 * T R (m + 1) * T R (m + k + 2) = T R (2 * m + k + 3) + T R (k + 1),
  { have h_nat₁ : m + 1 + (k + 1) = m + k + 2 := by ring,
    have h_nat₂ : 2 * (m + 1) + (k + 1) = 2 * m + k + 3 := by ring,
    simpa [h_nat₁, h_nat₂] using mul_T (m + 1) (k + 1) },
  -- clean up the `T` nat indices in the inductive hypothesis applied to `m` and `k + 2`
  have H₂ : 2 * T R m * T R (m + k + 2) = T R (2 * m + k + 2) + T R (k + 2),
  { have h_nat₁ : 2 * m + (k + 2) = 2 * m + k + 2 := by simp [add_assoc],
    have h_nat₂ : m + (k + 2) = m + k + 2 := by simp [add_assoc],
    simpa [h_nat₁, h_nat₂] using mul_T m (k + 2) },
  -- state the `T` recurrence relation for a few useful indices
  have h₁ := T_add_two R m,
  have h₂ := T_add_two R (2 * m + k + 2),
  have h₃ := T_add_two R k,
  -- the desired identity is an appropriate linear combination of H₁, H₂, h₁, h₂, h₃
  -- it would be really nice here to have a linear algebra tactic!!
  apply_fun (λ p, 2 * X * p) at H₁,
  apply_fun (λ p, 2 * T R (m + k + 2) * p) at h₁,
  have e₁ := congr (congr_arg has_add.add H₁) h₁,
  have e₂ := congr (congr_arg has_sub.sub e₁) H₂,
  have e₃ := congr (congr_arg has_sub.sub e₂) h₂,
  have e₄ := congr (congr_arg has_sub.sub e₃) h₃,
  rw ← sub_eq_zero at e₄ ⊢,
  rw ← e₄,
  ring,
end

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
lemma T_mul :
  ∀ m : ℕ, ∀ n : ℕ, T R (m * n) = (T R m).comp (T R n)
| 0 := by simp
| 1 := by simp
| (m + 2) := begin
  intros n,
  have : 2 * T R n * T R ((m + 1) * n) = T R ((m + 2) * n) + T R (m * n),
  { convert mul_T R n (m * n); ring },
  simp [this, T_mul m, ← T_mul (m + 1)]
end

end polynomial.chebyshev
