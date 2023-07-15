/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.complex.module
import ring_theory.norm
import ring_theory.trace

/-! # Lemmas about `algebra.trace` and `algebra.norm` on `ℂ` 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

open complex

lemma algebra.left_mul_matrix_complex (z : ℂ) :
  algebra.left_mul_matrix complex.basis_one_I z = !![z.re, -z.im; z.im, z.re] :=
begin
  ext i j,
  rw [algebra.left_mul_matrix_eq_repr_mul, complex.coe_basis_one_I_repr, complex.coe_basis_one_I,
    mul_re, mul_im, matrix.of_apply],
  fin_cases j,
  { simp_rw [matrix.cons_val_zero, one_re, one_im, mul_zero, mul_one, sub_zero, zero_add],
    fin_cases i; refl },
  { simp_rw [matrix.cons_val_one, matrix.head_cons, I_re, I_im, mul_zero, mul_one, zero_sub,
      add_zero],
    fin_cases i; refl },
end

lemma algebra.trace_complex_apply (z : ℂ) : algebra.trace ℝ ℂ z = 2*z.re :=
begin
  rw [algebra.trace_eq_matrix_trace complex.basis_one_I,
    algebra.left_mul_matrix_complex, matrix.trace_fin_two],
  exact (two_mul _).symm
end

lemma algebra.norm_complex_apply (z : ℂ) : algebra.norm ℝ z = z.norm_sq :=
begin
  rw [algebra.norm_eq_matrix_det complex.basis_one_I,
    algebra.left_mul_matrix_complex, matrix.det_fin_two, norm_sq_apply],
  simp,
end

lemma algebra.norm_complex_eq : algebra.norm ℝ = norm_sq.to_monoid_hom :=
monoid_hom.ext algebra.norm_complex_apply
