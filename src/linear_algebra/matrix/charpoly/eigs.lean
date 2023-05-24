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
* `matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the characteristic
polynomial.
* `matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the characteristic
polynomial.

Note that over other fields such as ` ℝ`, these results can be used by using `A.map (algebra_map ℝ ℂ)` as the matrix,
and then applying `ring_hom.map_det`.
-/
variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End
open_locale matrix big_operators

lemma prod_roots_charpoly_eq_det (A : matrix n n R) :
  (matrix.charpoly A).roots.prod = A.det :=
begin
  casesI is_empty_or_nonempty n,
  { have hdeg := charpoly_nat_degree_eq_dim A,
    rw [det_eq_sign_charpoly_coeff, ← hdeg,
      polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic
        (is_alg_closed.splits _),
      ← mul_assoc, ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul] },
  { rw not_nonempty_iff at hn,
    rw matrix.charpoly,
    repeat {rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn)},
    simp only [polynomial.roots_one, multiset.empty_eq_zero, multiset.prod_zero], },
end

lemma trace_eq_sum_roots_charpoly (A: matrix n n R) :
  A.trace = (matrix.charpoly A).roots.sum :=
begin
  casesI is_empty_or_nonempty n,
  { haveI hn1 := hn,
    apply_fun (has_neg.neg),
    rw ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split ,
    rw trace_eq_neg_charpoly_coeff, rw next_coeff,
    rw neg_neg, rw charpoly_nat_degree_eq_dim,
    have fn: 0 < fintype.card n, by apply (fintype.card_pos),
    have fne := ne_of_lt fn,
    symmetry' at fne,
    rw ne.def at fne,
    split_ifs, refl,
    apply matrix.charpoly_monic,
    exact is_alg_closed.splits A.charpoly,
    rintros a x hax, rwa neg_inj at hax, },
  { rw not_nonempty_iff at hn,
    rw [matrix.trace, fintype.sum_empty _],
    rw matrix.charpoly,
    rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn),
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.sum_zero],
    exact hn, },
end
