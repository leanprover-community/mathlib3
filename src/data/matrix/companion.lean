/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import ring_theory.adjoin_root
import linear_algebra.matrix.to_lin

/-!
# Companion matrices

## Main definitions

* `matrix.companion` : the companion matrix of a polynomial.

## Main statements

* `matrix.companion_eq_to_matrix_lmul_root` : The companion matrix of `P` is the matrix of the
  multiplication by `root P` in the canonical basis `1, root P, (root P)^2, ...` of `adjoin_root P`.

## Tags

Companion matrix, Frobenius matrix
-/

open_locale polynomial

namespace matrix
variables {R : Type*}

/--The companion matrix of a polynomial.-/
def companion [ring R] (P : R[X]) : matrix (fin P.nat_degree) (fin P.nat_degree) R :=
if h : P.nat_degree = 0 then 0 else
  λ i j, if j = fin.last' h then -P.coeff i else if (j : ℕ) + 1 = i then 1 else 0

open adjoin_root polynomial

/--The companion matrix of `P` is the matrix of the multiplication by `root P` in the canonical
basis `1, root P, (root P)^2, ...` of `adjoin_root P`.-/
lemma companion_eq_to_matrix_lmul_root [comm_ring R] {P : R[X]} (hP : P.monic) :
  companion P = alg_equiv_matrix (power_basis' hP).basis (algebra.lmul _ _ (root P)) :=
begin
  dunfold companion, split_ifs with h,
  { haveI : subsingleton (matrix (fin P.nat_degree) (fin P.nat_degree) R),
    { rw h, exact subsingleton_of_empty_left },
    rw eq_iff_true_of_subsingleton, trivial },
  change _ = linear_map.to_matrix _ _ _,
  ext i j,
  rw [linear_map.to_matrix_apply, algebra.lmul_apply, power_basis.basis_eq_pow, power_basis'_gen,
    ← pow_succ, ← mk_X, ← map_pow, ← monomial_one_right_eq_X_pow],
  dsimp [power_basis'],
  rw [mod_by_monic_eq_sub_mul_div _ hP, coeff_sub, coeff_monomial],
  by_cases hj : j = fin.last' h,
  { suffices : monomial P.nat_degree 1 /ₘ P = 1,
    from by rw [if_pos hj, hj, fin.coe_last', nat.sub_add_cancel $ nat.pos_of_ne_zero h,
      if_neg $ ne_of_gt i.is_lt, zero_sub, this, mul_one],
    nontriviality R,
    rw [← monic.nat_degree_eq_zero_iff_eq_one, nat_degree_div_by_monic _ hP,
      nat_degree_monomial_eq _ (@one_ne_zero R _ _), nat.sub_self],
    rw [monic.def, leading_coeff_div_by_monic_of_monic hP, leading_coeff_monomial],
    rw degree_monomial _ (@one_ne_zero R _ _), exact degree_le_nat_degree },
  { suffices : monomial (j + 1) 1 /ₘ P = 0,
    from by rw [if_neg hj, this, mul_zero, coeff_zero, sub_zero],
    nontriviality R,
    rw [div_by_monic_eq_zero_iff hP, degree_monomial _ (@one_ne_zero R _ _),
      degree_eq_nat_degree hP.ne_zero, with_bot.coe_lt_coe],
    apply lt_of_le_of_ne,
    { rw nat.add_one_le_iff, exact j.is_lt },
    { intro hj', apply hj, ext, simp_rw [fin.coe_last', ← hj', nat.add_sub_cancel] } }
end

lemma minpoly_companion [field R] {P : R[X]} (hP : P.monic) : minpoly R (companion P) = P :=
eq.symm $ minpoly.unique _ _ hP
(by rw [companion_eq_to_matrix_lmul_root hP, aeval_alg_equiv_apply, aeval_alg_hom_apply, aeval_eq,
    mk_self, map_zero, map_zero]) $
λ q hq Pq, begin
  rw [companion_eq_to_matrix_lmul_root hP, aeval_alg_equiv_apply, aeval_alg_hom_apply, aeval_eq,
    add_equiv_class.map_eq_zero_iff, map_eq_zero_iff, mk_eq_zero] at Pq,
  rw [degree_eq_nat_degree hP.ne_zero, degree_eq_nat_degree hq.ne_zero, with_bot.coe_le_coe],
  exact nat_degree_le_of_dvd Pq hq.ne_zero,
  { exact algebra.lmul_injective' _ _ }
end

end matrix
