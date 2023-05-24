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

## Two Lemmas
In algebraically closed fields the following two lemmas are available:
  (or when one is willing to extend the working field to such fields like ℝ to ℂ):
- `det_eq_prod_roots_charpoly` determinant is the product of the roots of the characteristic
polynomial.
- `trace_eq_sum_roots_charpoly` trace of a matrix is the sum of the roots of the characteristic
polynomial.
-/
variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End
open_locale matrix big_operators

lemma det_eq_prod_roots_charpoly (A : matrix n n R):
  (matrix.charpoly A).roots.prod = A.det :=
begin
  by_cases hn: nonempty n,
  { have hdeg := charpoly_nat_degree_eq_dim A,
    rw [det_eq_sign_charpoly_coeff, ← hdeg,
      polynomial.prod_roots_eq_coeff_zero_of_monic_of_split,
      ← mul_assoc, ← pow_two, ← pow_mul ],

    by_cases h2: ring_char R ≠ 2,
    { have hstupid: -1 ≠ (1:R), {exact ring.neg_one_ne_one_of_char_ne_two h2,},
      have hs2 : even(A.charpoly.nat_degree*2), {simp only [even.mul_left, even_two],},
      rw [(neg_one_pow_eq_one_iff_even hstupid).2 hs2, one_mul],},
    { rw [ne.def, not_not] at h2,
      rw [neg_one_eq_one_iff.2 h2, one_pow, one_mul],},

    apply matrix.charpoly_monic,
    exact is_alg_closed.splits A.charpoly, },
  { rw not_nonempty_iff at hn,
    rw matrix.charpoly,
    repeat {rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn)},
    simp only [polynomial.roots_one, multiset.empty_eq_zero, multiset.prod_zero], },
end

lemma trace_eq_sum_roots_charpoly (A: matrix n n R) :
  (matrix.charpoly A).roots.sum = A.trace  :=
begin
  by_cases hn: (nonempty n),
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
