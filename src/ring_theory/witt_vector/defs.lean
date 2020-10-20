/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.structure_polynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.

-/

noncomputable theory

namespace witt_vector

variables (p : ℕ) {R : Type*} [hp : fact p.prime] [comm_ring R]
include hp
open mv_polynomial

section ring_operations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def witt_zero : ℕ → mv_polynomial (fin 0 × ℕ) ℤ :=
witt_structure_int p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def witt_one : ℕ → mv_polynomial (fin 0 × ℕ) ℤ :=
witt_structure_int p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def witt_add : ℕ → mv_polynomial (fin 2 × ℕ) ℤ :=
witt_structure_int p (X 0 + X 1)

/-- The polynomials used for describing the subtraction of the ring of Witt vectors.
Note that `a - b` is defined as `a + -b`.
See `witt_vector.sub_coeff` for a proof that subtraction is precisely
given by these polynomials `witt_vector.witt_sub` -/
def witt_sub : ℕ → mv_polynomial (fin 2 × ℕ) ℤ :=
witt_structure_int p (X 0 - X 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def witt_mul : ℕ → mv_polynomial (fin 2 × ℕ) ℤ :=
witt_structure_int p (X 0 * X 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def witt_neg : ℕ → mv_polynomial (fin 1 × ℕ) ℤ :=
witt_structure_int p (-X 0)

end ring_operations

section witt_structure_simplifications

@[simp] lemma witt_zero_eq_zero (n : ℕ) : witt_zero p n = 0 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_zero, witt_structure_rat, bind₁, aeval_zero',
    constant_coeff_X_in_terms_of_W, ring_hom.map_zero,
    alg_hom.map_zero, map_witt_structure_int],
end

@[simp] lemma witt_one_zero_eq_one : witt_one p 0 = 1 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_one, witt_structure_rat, X_in_terms_of_W_zero, alg_hom.map_one,
    ring_hom.map_one, bind₁_X_right, map_witt_structure_int]
end

@[simp] lemma witt_one_pos_eq_zero (n : ℕ) (hn : 0 < n) : witt_one p n = 0 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_one, witt_structure_rat, ring_hom.map_zero, alg_hom.map_one,
    ring_hom.map_one, map_witt_structure_int],
  revert hn, apply nat.strong_induction_on n, clear n,
  intros n IH hn,
  rw X_in_terms_of_W_eq,
  simp only [alg_hom.map_mul, alg_hom.map_sub, alg_hom.map_sum, alg_hom.map_pow,
    bind₁_X_right, bind₁_C_right],
  rw [sub_mul, one_mul],
  rw [finset.sum_eq_single 0],
  { simp only [inv_of_eq_inv, one_mul, inv_pow', nat.sub_zero, ring_hom.map_one, pow_zero],
    simp only [one_pow, one_mul, X_in_terms_of_W_zero, sub_self, bind₁_X_right] },
  { intros i hin hi0,
    rw [finset.mem_range] at hin,
    rw [IH _ hin (nat.pos_of_ne_zero hi0), zero_pow (pow_pos hp.pos _), mul_zero], },
  { rw finset.mem_range, intro, contradiction }
end

@[simp] lemma witt_add_zero : witt_add p 0 = X (0,0) + X (1,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_add, witt_structure_rat, alg_hom.map_add, ring_hom.map_add,
    rename_X, X_in_terms_of_W_zero, map_X,
     witt_polynomial_zero, bind₁_X_right, map_witt_structure_int],
end

@[simp] lemma witt_sub_zero : witt_sub p 0 = X (0,0) - X (1,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_sub, witt_structure_rat, alg_hom.map_sub, ring_hom.map_sub,
    rename_X, X_in_terms_of_W_zero, map_X,
     witt_polynomial_zero, bind₁_X_right, map_witt_structure_int],
end

@[simp] lemma witt_mul_zero : witt_mul p 0 = X (0,0) * X (1,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_mul, witt_structure_rat, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, ring_hom.map_mul,
    bind₁_X_right, alg_hom.map_mul, map_witt_structure_int]
end

@[simp] lemma witt_neg_zero : witt_neg p 0 = - X (0,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_neg, witt_structure_rat, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, ring_hom.map_neg,
   alg_hom.map_neg, bind₁_X_right, map_witt_structure_int]
end

@[simp] lemma constant_coeff_witt_add (n : ℕ) :
  constant_coeff (witt_add p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [add_zero, ring_hom.map_add, constant_coeff_X],
end

@[simp] lemma constant_coeff_witt_sub (n : ℕ) :
  constant_coeff (witt_sub p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [sub_zero, ring_hom.map_sub, constant_coeff_X],
end

@[simp] lemma constant_coeff_witt_mul (n : ℕ) :
  constant_coeff (witt_mul p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [mul_zero, ring_hom.map_mul, constant_coeff_X],
end

@[simp] lemma constant_coeff_witt_neg (n : ℕ) :
  constant_coeff (witt_neg p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [neg_zero, ring_hom.map_neg, constant_coeff_X],
end

end witt_structure_simplifications

lemma witt_add_vars (n : ℕ) :
  (witt_add p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

lemma witt_mul_vars (n : ℕ) :
  (witt_mul p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

lemma witt_neg_vars (n : ℕ) :
  (witt_neg p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

end witt_vector
