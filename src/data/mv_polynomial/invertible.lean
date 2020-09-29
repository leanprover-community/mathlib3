/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin and Robert Y. Lewis
-/

import data.mv_polynomial.basic
import algebra.invertible

/-!
# Invertible polynomials

This file is a stub containing some basic facts about invertible elements in the ring of polynomials.
-/

open mv_polynomial

/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any `ℚ`-algebra. -/
def invertible_rat_algebra_coe_nat (R : Type*) (p : ℕ)
  [semiring R] [algebra ℚ R] [invertible (p : ℚ)] :
  invertible (p : R) :=
invertible.copy (invertible.map (algebra_map ℚ R : ℚ →* R) p) p
  (by simp only [ring_hom.map_nat_cast, coe_monoid_hom])

noncomputable instance mv_polynomial.invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance mv_polynomial.invertible_rat_coe_nat
  (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
invertible_rat_algebra_coe_nat _ _
