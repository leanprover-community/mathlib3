/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.power_series
import tactic

/-!
# Generating functions

-/

def generating_function {R : Type*} [comm_semiring R] (a : ℕ → R) :
  power_series R :=
power_series.mk a

@[simp] lemma coeff_generating_function {R : Type*} [comm_semiring R] (a : ℕ → R) (n : ℕ) :
  power_series.coeff R n (generating_function a) = a n :=
power_series.coeff_mk _ _

def exponential_generating_function {K : Type*} [discrete_field K] (a : ℕ → K) :
  power_series K :=
power_series.mk $ λ n, a n / n.fact

def bell_series {R : Type*} [comm_semiring R] (p : ℕ) (a : ℕ → R) :
  power_series R :=
power_series.mk $ λ n, a (p^n)

def geometric_sequence {G : Type*} [monoid G] (x : G) (n : ℕ) := x^n

@[simp] lemma geometric_sequence_one (G : Type*) [monoid G] :
  geometric_sequence (1 : G) = λ n, 1 :=
funext $ λ n, one_pow n

section
open power_series

@[simp] lemma units.coe_mk_of_mul_eq_one {G : Type*} [comm_monoid G] {x y : G} (h : x * y = 1) :
  (units.mk_of_mul_eq_one x y h : G) = x := rfl

@[simp] lemma power_series.coeff_mul_C {R : Type*} [comm_semiring R] (n : ℕ) (φ : power_series R) (r : R) :
  coeff R n (φ * (C R r)) = (coeff R n φ) * r :=
begin
  rw [coeff_mul n φ, finset.sum_eq_single (n,0)],
  { rw [coeff_C, if_pos rfl] },
  { rintro ⟨i,j⟩ hij hne,
    by_cases hj : j = 0,
    { subst hj, simp at *, contradiction },
    { simp [coeff_C, hj] } },
  { intro h, exfalso, apply h, simp },
end

@[simp] lemma power_series.coeff_succ_mul_X {R : Type*} [comm_semiring R] (n : ℕ) (φ : power_series R) :
  coeff R (n+1) (φ * X) = (coeff R n φ) :=
begin
  rw [coeff_mul _ φ, finset.sum_eq_single (n,1)],
  { rw [coeff_X, if_pos rfl, mul_one] },
  { rintro ⟨i,j⟩ hij hne,
    by_cases hj : j = 1,
    { subst hj, simp at *, contradiction },
    { simp [coeff_X, hj] } },
  { intro h, exfalso, apply h, simp },
end

@[simp] lemma power_series.coeff_zero_mul_X {R : Type*} [comm_semiring R] (φ : power_series R) :
  coeff R 0 (φ * X) = 0 :=
begin
  rw [coeff_mul _ φ, finset.sum_eq_zero],
  rintro ⟨i,j⟩ hij,
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0, { simpa using hij },
  simp,
end

lemma generating_function_geometric_sequence {K : Type*} [discrete_field K] (x : K) :
  generating_function (geometric_sequence x) = (1 - C K x * X)⁻¹ :=
begin
  have invertible : (1 - C K x * X) * (1 - C K x * X)⁻¹ = 1,
  { apply power_series.mul_inv,
    simpa only [ring_hom.map_sub, ring_hom.map_mul, ring_hom.map_one,
      constant_coeff_X, mul_zero, sub_zero] using one_ne_zero },
  suffices : generating_function (geometric_sequence x) * (1 - ((C K) x * X)) = 1,
  { apply (units.mul_right_inj (units.mk_of_mul_eq_one _ _ invertible)).mp,
    simpa [invertible] },
  ext n,
  rw [mul_sub, mul_one, add_monoid_hom.map_sub, coeff_one, ← mul_assoc],
  rw [coeff_generating_function (geometric_sequence x)],
  cases n,
  { rw [power_series.coeff_zero_mul_X ((generating_function (geometric_sequence x)) * C K x)],
    simp [geometric_sequence] },
  { rw [power_series.coeff_succ_mul_X n ((generating_function (geometric_sequence x)) * C K x)],
    rw [power_series.coeff_mul_C n (generating_function (geometric_sequence x))],
    rw [coeff_generating_function (geometric_sequence x)],
    simp [geometric_sequence, pow_succ', if_neg (nat.succ_ne_zero n)] }
end

lemma generating_function_const_one (K : Type*) [discrete_field K] :
  generating_function (λ n, (1 : K)) = (1 - X)⁻¹ :=
calc generating_function (λ n, (1 : K))
      = generating_function (geometric_sequence 1) : by simp
  ... = (1 - C K 1 * X)⁻¹                          : generating_function_geometric_sequence 1
  ... = (1 - X)⁻¹                                  : by simp

end
