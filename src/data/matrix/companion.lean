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
* `matrix.minpoly_companion` : The minimal polynomial of the companion matrix of `P` is `P`.

## Tags

Companion matrix, Frobenius matrix
-/

open_locale polynomial

namespace matrix
variables {R : Type*}

/-- The companion matrix of a polynomial. -/
def companion [ring R] (P : R[X]) : matrix (fin P.nat_degree) (fin P.nat_degree) R :=
if h : P.nat_degree = 0 then 0 else
  λ i j, if j = fin.last' h then -P.coeff i else if (j : ℕ) + 1 = i then 1 else 0

@[simp] lemma companion_apply_last [ring R] (P : R[X]) {i j : fin P.nat_degree}
  (hj : (j : ℕ) + 1 = P.nat_degree) : companion P i j = -P.coeff i :=
begin
  dunfold companion,
  split_ifs with h hj',
  { refine (is_empty_iff.mp _ i).elim, rw h, apply_instance },
  { refl },
  { refine (hj' _).elim, ext, simp_rw [fin.coe_last', ← hj, nat.add_sub_cancel] },
  { refine (hj' _).elim, ext, simp_rw [fin.coe_last', ← hj, nat.add_sub_cancel] }
end

@[simp] lemma companion_apply_eq_one [ring R] (P : R[X]) {i j : fin P.nat_degree}
  (hj : (j : ℕ) + 1 = i) : companion P i j = 1 :=
begin
  dunfold companion,
  split_ifs with h hj',
  { refine (is_empty_iff.mp _ i).elim, rw h, apply_instance },
  { refine (not_le.mpr i.is_lt _).elim,
    rw [hj', fin.coe_last'] at hj,
    rw ← hj, exact le_tsub_add },
  { refl }
end

@[simp] lemma companion_apply_eq_zero [ring R] (P : R[X]) {i j : fin P.nat_degree}
  (hj : (j : ℕ) + 1 ≠ P.nat_degree) (hji : (j : ℕ) + 1 ≠ i) : companion P i j = 0 :=
begin
  dunfold companion,
  split_ifs with h hj',
  { refine (is_empty_iff.mp _ i).elim, rw h, apply_instance },
  { refine (hj _).elim, rw [hj', fin.coe_last', nat.sub_add_cancel $ nat.pos_of_ne_zero h] },
  { refl }
end

open polynomial

@[simp] lemma companion_monomial [ring R] {n : ℕ} {c : R} :
  companion (monomial n c) = λ i j, if (j : ℕ) + 1 = i then 1 else 0 :=
begin
  ext i j,
  split_ifs with h,
  { exact companion_apply_eq_one _ h },
  { by_cases hj : (j : ℕ) + 1 = (monomial n c).nat_degree,
    { rw [companion_apply_last _ hj, coeff_monomial, neg_eq_zero],
      by_cases hc : c = 0, { split_ifs, exact hc, refl },
      simp_rw [hj, nat_degree_monomial_eq _ hc] at h, exact if_neg h },
    { exact companion_apply_eq_zero _ hj h } }
end

open adjoin_root

/-- The companion matrix of `P` is the matrix of the multiplication by `root P` in the canonical
basis `1, root P, (root P)^2, ...` of `adjoin_root P`. -/
lemma companion_eq_to_matrix_lmul_root [comm_ring R] {P : R[X]} (hP : P.monic) :
  companion P = alg_equiv_matrix (power_basis' hP).basis (algebra.lmul _ _ (root P)) :=
begin
  change _ = linear_map.to_matrix _ _ _,
  ext i j,
  rw [linear_map.to_matrix_apply, algebra.lmul_apply, power_basis.basis_eq_pow, power_basis'_gen,
    ← pow_succ, ← mk_X, ← map_pow, ← monomial_one_right_eq_X_pow],
  dsimp [power_basis'],
  rw [mod_by_monic_eq_sub_mul_div _ hP, coeff_sub, coeff_monomial],
  by_cases hj : (j : ℕ) + 1 = P.nat_degree,
  { suffices : monomial P.nat_degree 1 /ₘ P = 1,
    from by rw [companion_apply_last P hj, hj, if_neg $ ne_of_gt i.is_lt, zero_sub, this, mul_one],
    nontriviality R,
    rw [← monic.nat_degree_eq_zero_iff_eq_one, nat_degree_div_by_monic _ hP,
      nat_degree_monomial_eq _ (@one_ne_zero R _ _), nat.sub_self],
    rw [monic.def, leading_coeff_div_by_monic_of_monic hP, leading_coeff_monomial],
    rw degree_monomial _ (@one_ne_zero R _ _), exact degree_le_nat_degree },
  { suffices : monomial (j + 1) 1 /ₘ P = 0,
    { rw [this, mul_zero, coeff_zero, sub_zero],
      split_ifs with hi,
      { exact companion_apply_eq_one P hi },
      { exact companion_apply_eq_zero P hj hi } },
    nontriviality R,
    rw [div_by_monic_eq_zero_iff hP, degree_monomial _ (@one_ne_zero R _ _),
      degree_eq_nat_degree hP.ne_zero, with_bot.coe_lt_coe],
    exact lt_of_le_of_ne (nat.add_one_le_iff.mpr j.is_lt) hj }
end

/-- The minimal polynomial of the companion matrix of `P` is `P`. -/
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
