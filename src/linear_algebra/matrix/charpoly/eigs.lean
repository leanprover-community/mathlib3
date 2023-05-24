/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.polynomial.basic
import field_theory.is_alg_closed.basic
import algebra.char_p.two

/-!
# Eigenvalues are characteristic polynomial roots.


In algebraically closed fields, we show:
* `matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
characteristic polynomial.
* `matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the characteristic
polynomial.

Note that over other fields such as ` ℝ`, these results can be used by using
`A.map (algebra_map ℝ ℂ)` as the matrix, and then applying `ring_hom.map_det`.

The two lemmas `matrix.det_eq_prod_roots_charpoly` and `matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `linear_algebra.eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.
-/
variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End
open_locale matrix big_operators

lemma det_eq_prod_roots_charpoly (A : matrix n n R) :
  A.det = (matrix.charpoly A).roots.prod :=
begin
  casesI is_empty_or_nonempty n,
  { rw matrix.charpoly,
    repeat {rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 h)},
    simp only [polynomial.roots_one, multiset.empty_eq_zero, multiset.prod_zero], },
  { have hdeg := charpoly_nat_degree_eq_dim A,
    rw [det_eq_sign_charpoly_coeff, ← hdeg,
      polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic
        (is_alg_closed.splits _),
      ← mul_assoc, ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul], },
end

lemma trace_eq_sum_roots_charpoly (A: matrix n n R) :
  A.trace = (matrix.charpoly A).roots.sum :=
begin
  casesI is_empty_or_nonempty n,
  { rw [matrix.trace, fintype.sum_empty],
    rw matrix.charpoly,
    rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 h),
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.sum_zero],},
  { rw [← neg_inj, ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split A.charpoly_monic
      (is_alg_closed.splits A.charpoly),
      trace_eq_neg_charpoly_coeff, next_coeff, neg_neg,
      charpoly_nat_degree_eq_dim],
    have fne := (ne_of_lt (@fintype.card_pos _ _ h)).symm,
    rw ne.def at fne,
    split_ifs,
    refl, },
end
