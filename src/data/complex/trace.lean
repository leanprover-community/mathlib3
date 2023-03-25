/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import ring_theory.trace
import data.complex.module

/-! # Lemmas about `algebra.trace` on `ℂ` -/

lemma algebra.trace_complex_apply (z : ℂ) : algebra.trace ℝ ℂ z = 2*z.re :=
begin
  classical,
  rw [algebra.trace_apply, linear_map.trace_eq_matrix_trace ℝ complex.basis_one_I,
    matrix.trace],
  simp_rw [matrix.diag, linear_map.to_matrix_apply, complex.coe_basis_one_I_repr, fin.sum_univ_two,
    complex.coe_basis_one_I, algebra.coe_lmul_eq_mul, linear_map.mul_apply'],
  simp [two_mul],
end
