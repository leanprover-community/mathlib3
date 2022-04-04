/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.induction
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
@[simps]
def op_ring_equiv (R : Type*) [semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
((to_finsupp_iso R).op.trans add_monoid_algebra.op_ring_equiv).trans (to_finsupp_iso _).symm

@[simp] lemma op_ring_equiv_op_monomial (n : ℕ) (r : R) :
  (op_ring_equiv R) (op (monomial n r : R[X])) = monomial n (op r) :=
by simp only [op_ring_equiv, ring_equiv.trans_apply, ring_equiv.op_apply_apply,
    ring_equiv.to_add_equiv_eq_coe, add_equiv.mul_op_apply, add_equiv.to_fun_eq_coe,
    add_equiv.coe_trans, op_add_equiv_apply, ring_equiv.coe_to_add_equiv, op_add_equiv_symm_apply,
    function.comp_app, unop_op, to_finsupp_iso_monomial, add_monoid_algebra.op_ring_equiv_single,
    to_finsupp_iso_symm_single]

@[simp] lemma op_ring_equiv_op_C (a : R) :
  (op_ring_equiv R) (op (C a)) = C (op a) :=
op_ring_equiv_op_monomial 0 a

@[simp] lemma op_ring_equiv_op_X :
  (op_ring_equiv R) (op (X : R[X])) = X :=
op_ring_equiv_op_monomial 1 1

lemma op_ring_equiv_op_C_mul_X_pow (r : R) (n : ℕ) :
  (op_ring_equiv R) (op (C r * X ^ n : R[X])) = C (op r) * X ^ n :=
by simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, op_ring_equiv_op_X, op_ring_equiv_op_C]

@[simp] lemma coeff_op_ring_equiv (p : R[X]ᵐᵒᵖ) (n : ℕ) :
  (op_ring_equiv R p).coeff n = op ((unop p).coeff n) :=
begin
  nth_rewrite 0 ← op_unop p,
  generalize' hp' : unop p = p',
  apply p'.induction_on,
  { intros a,
    by_cases n0 : n = 0,
    { simp only [coeff_C, n0, op_ring_equiv_op_C, eq_self_iff_true, if_true] },
    { simp only [coeff_C, n0, op_ring_equiv_op_C, if_false, op_zero] } },
  { intros f g hf hg,
    simp only [hf, hg, op_add, _root_.map_add, coeff_add] },
  { intros m r hm,
    rw [op_ring_equiv_op_C_mul_X_pow, coeff_C_mul, coeff_C_mul, op_mul, coeff_X_pow, coeff_X_pow],
    split_ifs;
    simp }
end

@[simp] lemma support_op_ring_equiv (p : R[X]ᵐᵒᵖ) :
  (op_ring_equiv R p).support = (unop p).support :=
begin
  ext,
  rw [mem_support_iff, mem_support_iff, ne.def, coeff_op_ring_equiv],
  simp only [op_eq_zero_iff],
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
