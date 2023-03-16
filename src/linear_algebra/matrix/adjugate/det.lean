/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.matrix.adjugate.basic
import linear_algebra.matrix.mv_polynomial

/-!
# Additional facts about adjugates

We split off two facts about adjugates from the main file,
as they require importing more of the development of `mv_polynomial`,
which is not otherwise needed.

## Main definitions

 * `matrix.det_adjugate A`: `(adjugate A).det = A.det ^ (fintype.card n - 1)`.
 * `matrix.adjugate_adjugate A`: `adjugate (adjugate A) = det A ^ (fintype.card n - 2) • A`

## Tags

cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v
variables {n : Type u} [decidable_eq n] [fintype n] {α : Type v} [comm_ring α]
open_locale matrix big_operators polynomial
open equiv equiv.perm finset

section adjugate

lemma det_adjugate (A : matrix n n α) : (adjugate A).det = A.det ^ (fintype.card n - 1) :=
begin
  -- get rid of the `- 1`
  cases (fintype.card n).eq_zero_or_pos with h_card h_card,
  { haveI : is_empty n := fintype.card_eq_zero_iff.mp h_card,
    rw [h_card, nat.zero_sub, pow_zero, adjugate_subsingleton, det_one] },
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le,

  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mv_polynomial_X n n ℤ,
  suffices : A'.adjugate.det = A'.det ^ (fintype.card n - 1),
  { rw [←mv_polynomial_X_map_matrix_aeval ℤ A, ←alg_hom.map_adjugate, ←alg_hom.map_det,
      ←alg_hom.map_det, ←alg_hom.map_pow, this] },

  apply mul_left_cancel₀ (show A'.det ≠ 0, from det_mv_polynomial_X_ne_zero n ℤ),
  calc  A'.det * A'.adjugate.det
      = (A' ⬝ adjugate A').det                 : (det_mul _ _).symm
  ... = A'.det ^ fintype.card n                : by rw [mul_adjugate, det_smul, det_one, mul_one]
  ... = A'.det * A'.det ^ (fintype.card n - 1) : by rw [←pow_succ, h_card],
end

/-- Note that this is not true for `fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
lemma adjugate_adjugate (A : matrix n n α) (h : fintype.card n ≠ 1) :
  adjugate (adjugate A) = det A ^ (fintype.card n - 2) • A :=
begin
  -- get rid of the `- 2`
  cases h_card : (fintype.card n) with n',
  { haveI : is_empty n := fintype.card_eq_zero_iff.mp h_card,
    apply subsingleton.elim, },
  cases n',
  { exact (h h_card).elim },
  rw ←h_card,

  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mv_polynomial_X n n ℤ,
  suffices : adjugate (adjugate A') = det A' ^ (fintype.card n - 2) • A',
  { rw [←mv_polynomial_X_map_matrix_aeval ℤ A, ←alg_hom.map_adjugate, ←alg_hom.map_adjugate, this,
      ←alg_hom.map_det, ← alg_hom.map_pow, alg_hom.map_matrix_apply, alg_hom.map_matrix_apply,
      matrix.map_smul' _ _ _ (_root_.map_mul _)] },
  have h_card' : fintype.card n - 2 + 1 = fintype.card n - 1,
  { simp [h_card] },

  have is_reg : is_smul_regular (mv_polynomial (n × n) ℤ) (det A') :=
    λ x y, mul_left_cancel₀ (det_mv_polynomial_X_ne_zero n ℤ),
  apply is_reg.matrix,
  rw [smul_smul, ←pow_succ, h_card', det_smul_adjugate_adjugate],
end

/-- A weaker version of `matrix.adjugate_adjugate` that uses `nontrivial`. -/
lemma adjugate_adjugate' (A : matrix n n α) [nontrivial n] :
  adjugate (adjugate A) = det A ^ (fintype.card n - 2) • A :=
adjugate_adjugate _ $ fintype.one_lt_card.ne'

end adjugate

end matrix
