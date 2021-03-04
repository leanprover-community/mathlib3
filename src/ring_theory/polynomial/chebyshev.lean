/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Heather Macbeth
-/

import data.polynomial.derivative
import tactic.ring

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

## Main definitions

* `polynomial.chebyshev₁`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev₂`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `polynomial.mul_chebyshev₁`, the product of the `m`-th and `(m + k)`-th Chebyshev polynomials of
  the first kind is the sum of the `(2 * m + k)`-th and `k`-th Chebyshev polynomials of the first
  kind.
* `polynomial.chebyshev₁_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
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
  `ring_theory.polynomial.chebyshev.basic`.
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
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
by { simp only [chebyshev₂], ring, }

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
| 0        := by { simp only [chebyshev₂_zero, chebyshev₂_one, chebyshev₁_one], ring }
| 1        := by { simp only [chebyshev₂_one, chebyshev₁_two, chebyshev₂_two], ring }
| (n + 2)  :=
  calc chebyshev₂ R (n + 2 + 1) = 2 * X * (X * chebyshev₂ R (n + 1) + chebyshev₁ R (n + 2))
                                          - (X * chebyshev₂ R n + chebyshev₁ R (n + 1)) :
            by simp only [chebyshev₂_add_two, chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ n,
                                chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ (n + 1)]
  ... = X * (2 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n)
          + (2 * X * chebyshev₁ R (n + 2) - chebyshev₁ R (n + 1)) :
            by ring
  ... = X * chebyshev₂ R (n + 2) + chebyshev₁ R (n + 2 + 1) :
            by simp only [chebyshev₂_add_two, chebyshev₁_add_two]

lemma chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂ (n : ℕ) :
  chebyshev₁ R (n+1) = chebyshev₂ R (n+1) - X * chebyshev₂ R n :=
by rw [chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁, add_comm (X * chebyshev₂ R n), add_sub_cancel]


lemma chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂ :
  ∀ (n : ℕ), chebyshev₁ R (n+2) = X * chebyshev₁ R (n+1) - (1 - X ^ 2) * chebyshev₂ R n
| 0        := by { simp only [chebyshev₁_one, chebyshev₁_two, chebyshev₂_zero], ring }
| 1        := by { simp only [chebyshev₁_add_two, chebyshev₁_zero, chebyshev₁_add_two,
                              chebyshev₂_one, chebyshev₁_one], ring }
| (n + 2)  :=
calc chebyshev₁ R (n + 2 + 2)
    = 2 * X * chebyshev₁ R (n + 2 + 1) - chebyshev₁ R (n + 2) : chebyshev₁_add_two _ _
... = 2 * X * (X * chebyshev₁ R (n + 2) - (1 - X ^ 2) * chebyshev₂ R (n + 1))
      - (X * chebyshev₁ R (n + 1) - (1 - X ^ 2) * chebyshev₂ R n) :
            by simp only [chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂]
... = X * (2 * X * chebyshev₁ R (n + 2) -  chebyshev₁ R (n + 1))
      - (1 - X ^ 2) * (2 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n) :
            by ring
... = X * chebyshev₁ R (n + 2 + 1) - (1 - X ^ 2) * chebyshev₂ R (n + 2) :
            by rw [chebyshev₁_add_two _ (n + 1), chebyshev₂_add_two]

lemma one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁ (n : ℕ) :
  (1 - X ^ 2) * chebyshev₂ R n = X * chebyshev₁ R (n + 1) - chebyshev₁ R (n + 2) :=
by rw [chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂, ←sub_add, sub_self, zero_add]

variables {R S}

@[simp] lemma map_chebyshev₂ (f : R →+* S) :
  ∀ (n : ℕ), map f (chebyshev₂ R n) = chebyshev₂ S n
| 0       := by simp only [chebyshev₂_zero, map_one]
| 1       :=
begin
  simp only [chebyshev₂_one, map_X, map_mul, map_add, map_one],
  change map f (1+1) * X = 2 * X,
  simpa only [map_add, map_one]
end
| (n + 2) :=
begin
  simp only [chebyshev₂_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_chebyshev₂ (n + 1), map_chebyshev₂ n],
end

lemma chebyshev₁_derivative_eq_chebyshev₂ :
  ∀ (n : ℕ), derivative (chebyshev₁ R (n + 1)) = (n + 1) * chebyshev₂ R n
| 0        := by simp only [chebyshev₁_one, chebyshev₂_zero, derivative_X, nat.cast_zero, zero_add,
                           mul_one]
| 1        := by { simp only [chebyshev₁_two, chebyshev₂_one, derivative_sub, derivative_one,
                              derivative_mul, derivative_X_pow, nat.cast_one,
                              nat.cast_two],
                    norm_num }
| (n + 2)  :=
  calc derivative (chebyshev₁ R (n + 2 + 1))
      = 2 * chebyshev₁ R (n + 2) + 2 * X * derivative (chebyshev₁ R (n + 1 + 1))
                                 - derivative (chebyshev₁ R (n + 1)) :
              by simp only [chebyshev₁_add_two _ (n + 1), derivative_sub, derivative_mul,
                                      derivative_X, derivative_bit0, derivative_one, bit0_zero,
                                      zero_mul, zero_add, mul_one]
  ... = 2 * (chebyshev₂ R (n + 1 + 1) - X * chebyshev₂ R (n + 1))
        + 2 * X * ((n + 1 + 1) * chebyshev₂ R (n + 1)) - (n + 1) * chebyshev₂ R n :
              by rw_mod_cast [chebyshev₁_derivative_eq_chebyshev₂,
                chebyshev₁_derivative_eq_chebyshev₂, chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂]
  ... = (n + 1) * (2 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n) + 2 * chebyshev₂ R (n + 2) :
              by ring
  ... = (n + 1) * chebyshev₂ R (n + 2) + 2 * chebyshev₂ R (n + 2) :
              by rw chebyshev₂_add_two
  ... = (n + 2 + 1) * chebyshev₂ R (n + 2) :
              by ring
  ... = (↑(n + 2) + 1) * chebyshev₂ R (n + 2) :
              by norm_cast

lemma one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁ (n : ℕ) :
  (1 - X ^ 2)  * (derivative (chebyshev₁ R (n+1))) =
    (n + 1) * (chebyshev₁ R n - X * chebyshev₁ R (n+1)) :=
  calc
  (1 - X ^ 2)  * (derivative (chebyshev₁ R (n+1)))
  = (1 - X ^ 2 ) * ((n + 1) * chebyshev₂ R n) :
            by rw chebyshev₁_derivative_eq_chebyshev₂
  ... = (n + 1) * ((1 - X ^ 2) * chebyshev₂ R n) :
            by ring
  ... = (n + 1) * (X * chebyshev₁ R (n + 1) - (2 * X * chebyshev₁ R (n + 1) - chebyshev₁ R n)) :
            by rw [one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁, chebyshev₁_add_two]
  ... = (n + 1) * (chebyshev₁ R n - X * chebyshev₁ R (n+1)) :
            by ring

lemma add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂ (n : ℕ) :
  ((n : polynomial R) + 1) * chebyshev₁ R (n+1) =
    X * chebyshev₂ R n - (1 - X ^ 2) * derivative ( chebyshev₂ R n) :=
begin
  have h : derivative (chebyshev₁ R (n + 2)) = (chebyshev₂ R (n + 1) - X * chebyshev₂ R n)
    + X * derivative (chebyshev₁ R (n + 1)) + 2 * X * chebyshev₂ R n
    - (1 - X ^ 2) * derivative (chebyshev₂ R n),
  { conv_lhs { rw chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂ },
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
  one_mul, chebyshev₁_derivative_eq_chebyshev₂],
  rw [chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂, nat.cast_bit0, nat.cast_one],
  ring },
  calc ((n : polynomial R) + 1) * chebyshev₁ R (n + 1)
      = ((n : polynomial R) + 1 + 1) * (X * chebyshev₂ R n + chebyshev₁ R (n + 1))
        - X * ((n + 1) * chebyshev₂ R n) - (X * chebyshev₂ R n + chebyshev₁ R (n + 1)) :
            by ring
  ... = derivative (chebyshev₁ R (n + 2)) - X * derivative (chebyshev₁ R (n + 1))
                                          - chebyshev₂ R (n + 1) :
            by rw [←chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁,
                  ←chebyshev₁_derivative_eq_chebyshev₂, ←nat.cast_one, ←nat.cast_add,
                  nat.cast_one, ←chebyshev₁_derivative_eq_chebyshev₂ (n + 1)]
  ... = (chebyshev₂ R (n + 1) - X * chebyshev₂ R n) + X * derivative (chebyshev₁ R (n + 1))
        + 2 * X * chebyshev₂ R n - (1 - X ^ 2) * derivative (chebyshev₂ R n)
        - X * derivative (chebyshev₁ R (n + 1)) - chebyshev₂ R (n + 1) :
            by rw h
  ... = X * chebyshev₂ R n - (1 - X ^ 2) * derivative (chebyshev₂ R n) :
            by ring,
end

variables (R)

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
lemma mul_chebyshev₁ :
  ∀ m : ℕ, ∀ k,
  2 * chebyshev₁ R m * chebyshev₁ R (m + k) = chebyshev₁ R (2 * m + k) + chebyshev₁ R k
| 0 := by simp [two_mul, add_mul]
| 1 := by simp [add_comm]
| (m + 2) := begin
  intros k,
  -- clean up the `chebyshev₁` nat indices in the goal
  suffices : 2 * chebyshev₁ R (m + 2) * chebyshev₁ R (m + k + 2)
    = chebyshev₁ R (2 * m + k + 4) + chebyshev₁ R k,
  { have h_nat₁ : 2 * (m + 2) + k = 2 * m + k + 4 := by ring,
    have h_nat₂ : m + 2 + k = m + k + 2 := by simp [add_comm, add_assoc],
    simpa [h_nat₁, h_nat₂] using this },
  -- clean up the `chebyshev₁` nat indices in the inductive hypothesis applied to `m + 1` and
  -- `k + 1`
  have H₁ : 2 * chebyshev₁ R (m + 1) * chebyshev₁ R (m + k + 2)
    = chebyshev₁ R (2 * m + k + 3) + chebyshev₁ R (k + 1),
  { have h_nat₁ : m + 1 + (k + 1) = m + k + 2 := by ring,
    have h_nat₂ : 2 * (m + 1) + (k + 1) = 2 * m + k + 3 := by ring,
    simpa [h_nat₁, h_nat₂] using mul_chebyshev₁ (m + 1) (k + 1) },
  -- clean up the `chebyshev₁` nat indices in the inductive hypothesis applied to `m` and `k + 2`
  have H₂ : 2 * chebyshev₁ R m * chebyshev₁ R (m + k + 2)
    = chebyshev₁ R (2 * m + k + 2) + chebyshev₁ R (k + 2),
  { have h_nat₁ : 2 * m + (k + 2) = 2 * m + k + 2 := by simp [add_assoc],
    have h_nat₂ : m + (k + 2) = m + k + 2 := by simp [add_assoc],
    simpa [h_nat₁, h_nat₂] using mul_chebyshev₁ m (k + 2) },
  -- state the `chebyshev₁` recurrence relation for a few useful indices
  have h₁ := chebyshev₁_add_two R m,
  have h₂ := chebyshev₁_add_two R (2 * m + k + 2),
  have h₃ := chebyshev₁_add_two R k,
  -- the desired identity is an appropriate linear combination of H₁, H₂, h₁, h₂, h₃
  -- it would be really nice here to have a linear algebra tactic!!
  apply_fun (λ p, 2 * X * p) at H₁,
  apply_fun (λ p, 2 * chebyshev₁ R (m + k + 2) * p) at h₁,
  have e₁ := congr (congr_arg has_add.add H₁) h₁,
  have e₂ := congr (congr_arg has_sub.sub e₁) H₂,
  have e₃ := congr (congr_arg has_sub.sub e₂) h₂,
  have e₄ := congr (congr_arg has_sub.sub e₃) h₃,
  rw ← sub_eq_zero at e₄ ⊢,
  rw ← e₄,
  ring,
end

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
lemma chebyshev₁_mul :
  ∀ m : ℕ, ∀ n : ℕ, chebyshev₁ R (m * n) = (chebyshev₁ R m).comp (chebyshev₁ R n)
| 0 := by simp
| 1 := by simp
| (m + 2) := begin
  intros n,
  have : 2 * chebyshev₁ R n * chebyshev₁ R ((m + 1) * n)
    = chebyshev₁ R ((m + 2) * n) + chebyshev₁ R (m * n),
  { convert mul_chebyshev₁ R n (m * n); ring },
  simp [this, chebyshev₁_mul m, ← chebyshev₁_mul (m + 1)]
end

end polynomial
