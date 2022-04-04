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
  induction p using mul_opposite.rec,
  cases p,
  refl
end

-- TODO: move to finsupp/basic
lemma finsupp.support_map_range_of_injective {ι α β} [has_zero α] [has_zero β]
  {e : α → β} (he0 : e 0 = 0) (f : ι →₀ α) (he : function.injective e) :
  (finsupp.map_range e he0 f).support = f.support :=
begin
  ext,
  simp only [finsupp.mem_support_iff, ne.def, finsupp.map_range_apply],
  exact he.ne_iff' he0,
end

@[simp] lemma support_op_ring_equiv (p : R[X]ᵐᵒᵖ) :
  (op_ring_equiv R p).support = (unop p).support :=
begin
  induction p using mul_opposite.rec,
  cases p,
  exact support_map_range_of_injective _ _ op_injective
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
