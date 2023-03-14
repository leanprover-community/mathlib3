/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.degree.definitions

/-!  #  Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`op_ring_equiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/

open_locale polynomial
open polynomial mul_opposite

variables {R : Type*} [semiring R] {p q : R[X]}

noncomputable theory

namespace polynomial

/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a polynomial
to the corresponding element of the opposite ring. -/
def op_ring_equiv (R : Type*) [semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
((to_finsupp_iso R).op.trans add_monoid_algebra.op_ring_equiv).trans (to_finsupp_iso _).symm

-- for maintenance purposes: `by simp [op_ring_equiv]` proves this lemma
/-!  Lemmas to get started, using `op_ring_equiv R` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/
@[simp] lemma op_ring_equiv_op_monomial (n : ℕ) (r : R) :
  op_ring_equiv R (op (monomial n r : R[X])) = monomial n (op r) :=
by simp only [op_ring_equiv, ring_equiv.trans_apply, ring_equiv.op_apply_apply,
    ring_equiv.to_add_equiv_eq_coe, add_equiv.mul_op_apply, add_equiv.to_fun_eq_coe,
    add_equiv.coe_trans, op_add_equiv_apply, ring_equiv.coe_to_add_equiv, op_add_equiv_symm_apply,
    function.comp_app, unop_op, to_finsupp_iso_apply, to_finsupp_monomial,
    add_monoid_algebra.op_ring_equiv_single, to_finsupp_iso_symm_apply, of_finsupp_single]

@[simp] lemma op_ring_equiv_op_C (a : R) :
  op_ring_equiv R (op (C a)) = C (op a) :=
op_ring_equiv_op_monomial 0 a

@[simp] lemma op_ring_equiv_op_X :
  op_ring_equiv R (op (X : R[X])) = X :=
op_ring_equiv_op_monomial 1 1

lemma op_ring_equiv_op_C_mul_X_pow (r : R) (n : ℕ) :
  op_ring_equiv R (op (C r * X ^ n : R[X])) = C (op r) * X ^ n :=
by simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, op_ring_equiv_op_X, op_ring_equiv_op_C]

/-!  Lemmas to get started, using `(op_ring_equiv R).symm` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/
@[simp] lemma op_ring_equiv_symm_monomial (n : ℕ) (r : Rᵐᵒᵖ) :
  (op_ring_equiv R).symm (monomial n r) = op (monomial n (unop r)) :=
(op_ring_equiv R).injective (by simp)

@[simp] lemma op_ring_equiv_symm_C (a : Rᵐᵒᵖ) :
  (op_ring_equiv R).symm (C a) = op (C (unop a)) :=
op_ring_equiv_symm_monomial 0 a

@[simp] lemma op_ring_equiv_symm_X :
  (op_ring_equiv R).symm (X : Rᵐᵒᵖ[X]) = op X :=
op_ring_equiv_symm_monomial 1 1

lemma op_ring_equiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : ℕ) :
  (op_ring_equiv R).symm (C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n) :=
by rw [C_mul_X_pow_eq_monomial, op_ring_equiv_symm_monomial, ← C_mul_X_pow_eq_monomial]

/-!  Lemmas about more global properties of polynomials and opposites. -/
@[simp] lemma coeff_op_ring_equiv (p : R[X]ᵐᵒᵖ) (n : ℕ) :
  (op_ring_equiv R p).coeff n = op ((unop p).coeff n) :=
begin
  induction p using mul_opposite.rec,
  cases p,
  refl
end

@[simp] lemma support_op_ring_equiv (p : R[X]ᵐᵒᵖ) :
  (op_ring_equiv R p).support = (unop p).support :=
begin
  induction p using mul_opposite.rec,
  cases p,
  exact finsupp.support_map_range_of_injective _ _ op_injective
end

@[simp] lemma nat_degree_op_ring_equiv (p : R[X]ᵐᵒᵖ) :
  (op_ring_equiv R p).nat_degree = (unop p).nat_degree :=
begin
  by_cases p0 : p = 0,
  { simp only [p0, _root_.map_zero, nat_degree_zero, unop_zero] },
  { simp only [p0, nat_degree_eq_support_max', ne.def, add_equiv_class.map_eq_zero_iff,
      not_false_iff, support_op_ring_equiv, unop_eq_zero_iff] }
end

@[simp] lemma leading_coeff_op_ring_equiv (p : R[X]ᵐᵒᵖ) :
  (op_ring_equiv R p).leading_coeff = op (unop p).leading_coeff :=
by rw [leading_coeff, coeff_op_ring_equiv, nat_degree_op_ring_equiv, leading_coeff]

end polynomial
