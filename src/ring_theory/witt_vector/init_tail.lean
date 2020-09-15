/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.basic
import ring_theory.witt_vector.is_poly
import ring_theory.witt_vector.witt_vector_preps

/-!

# `init` and `tail`

Given a Witt vecfor `x`, we are sometimes interested in its components before and after an index `n`.
This file defines those operations, proves that `init` is polynomial, and shows how that polynomial
interacts with `mv_polynomial.bind₁`.

## Main declarations

* `witt_vector.init x n`: the first `n` coefficients of `x`, as a Witt vector. All coefficients at
  indices ≥ `n` are 0.
* `witt_vector.tail x n`: the complementary part to `init`. All coefficients at indices < `n` are 0,
  otherwise they are the same as in `x`.

-/

variables {p : ℕ} [hp : fact p.prime] (n : ℕ) {R : Type*} [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

namespace tactic
namespace interactive
setup_tactic_parser

/--
`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.
-/
meta def init_ring (assert : parse (tk "using" >> parser.pexpr)?) : tactic unit := do
`[rw ext_iff,
  intros i,
  simp only [init, coeff_mk],
  split_ifs with hi; try {refl}],
match assert with
| none := skip
| some e := do
  `[simp only [add_coeff, mul_coeff, neg_coeff],
    apply eval₂_hom_congr' (ring_hom.ext_int _ _) _ rfl,
    rintro ⟨b, k⟩ h -],
  tactic.replace `h ```(%%e p _ h),
  `[simp only [finset.mem_range, finset.mem_product, true_and, finset.mem_univ] at h,
    have hk : k < n, by linarith,
    fin_cases b;
    simp only [function.uncurry, matrix.cons_val_zero, matrix.head_cons, coeff_mk, matrix.cons_val_one,
      coeff_mk, hk, if_true]]
end

end interactive
end tactic

namespace witt_vector
open mv_polynomial

section

local attribute [semireducible] witt_vector

/-- `witt_vector.init x n` is the Witt vector of which the first `n` coefficients are those from `x`
and all other coefficients are `0`.
See `witt_vector.tail` for the complementary part.
-/
def init (x : 𝕎 R) (n : ℕ) : 𝕎 R := mk p (λ k, if k < n then x.coeff k else 0)

/-- `witt_vector.tail x n` is the Witt vector of which the first `n` coefficients are `0`
and all other coefficients are those from `x`.
See `witt_vector.init` for the complementary part. -/
def tail (x : 𝕎 R) (n : ℕ) : 𝕎 R := mk p (λ k, if k < n then 0 else x.coeff k)

end

@[simp]
lemma init_init (x : 𝕎 R) (n : ℕ) :
  init (init x n) n = init x n :=
by init_ring

include hp

lemma init_add (x y : 𝕎 R) (n : ℕ) :
  init (x + y) n = init (init x n + init y n) n :=
by init_ring using witt_add_vars

lemma init_mul (x y : 𝕎 R) (n : ℕ) :
  init (x * y) n = init (init x n * init y n) n :=
by init_ring using witt_mul_vars

lemma init_neg (x : 𝕎 R) (n : ℕ) :
  init (-x) n = init (-init x n) n :=
by init_ring using witt_neg_vars

lemma init_sub (x y : 𝕎 R) (n : ℕ) :
  init (x - y) n = init (init x n - init y n) n :=
begin
  simp only [sub_eq_add_neg],
  rw [init_add, init_neg],
  conv_rhs { rw [init_add, init_init] },
end

section

variables (p)

omit hp

/-- `witt_vector.init x` is polynomial in the coefficients of `x`. -/
noncomputable
def init_is_poly (n : ℕ) : is_poly p (λ R _Rcr x, @init p R _Rcr x n) :=
{ poly := λ i, if i < n then X i else 0,
  coeff :=
  begin
    rintro i R _Rcr x,
    dsimp [init],
    split_ifs with hin,
    { rw [aeval_X] },
    { rw [alg_hom.map_zero] }
  end }

include hp

lemma bind₁_init_poly_witt_polynomial (n k : ℕ) :
  bind₁ (init_is_poly p (n+1)).poly (witt_polynomial p ℤ k) =
    expand (p ^ (k - n)) (witt_polynomial p ℤ (min n k)) :=
begin
  have aux : ∀ k : ℕ, p ^ k ≠ 0,
  { intro k, apply pow_ne_zero _ hp.ne_zero, },
  dsimp [init_is_poly, min],
  split_ifs with hk,
  { dsimp [witt_polynomial],
    have hk1 : n + 1 ≤ k + 1, by linarith,
    rw [← finset.sum_range_add_sum_Ico _ hk1, alg_hom.map_add],
    convert add_zero _ using 1,
    apply congr₂,
    { rw [alg_hom.map_sum, alg_hom.map_sum, finset.sum_congr rfl],
      intros i hi,
      rw [expand_monomial, bind₁_monomial],
      simp only [aux, finsupp.support_single_ne_zero, int.cast_coe_nat, finset.prod_singleton,
        ring_hom.eq_int_cast, finsupp.single_eq_same, C_pow, ne.def, not_false_iff, mul_ite,
        int.nat_cast_eq_coe_nat, mul_zero, zero_pow', ite_pow],
      rw finset.mem_range at hi,
      rw if_pos hi,
      rw [← pow_mul, ← nat.pow_add],
      congr' 3,
      unfreezingI { clear aux hp p hk1 },
      omega, },
    { rw [alg_hom.map_sum, finset.sum_eq_zero],
      intros i hi,
      simp only [bind₁_monomial, aux, finsupp.support_single_ne_zero, int.cast_coe_nat,
        finset.prod_singleton, ring_hom.eq_int_cast, finsupp.single_eq_same, C_pow, ne.def,
        not_false_iff, mul_ite, int.nat_cast_eq_coe_nat, mul_zero, zero_pow', ite_pow],
      rw finset.Ico.mem at hi,
      rw if_neg,
      apply not_lt_of_le hi.1 } },
  { push_neg at hk,
    rw [nat.sub_eq_zero_of_le (le_of_lt hk), nat.pow_zero, expand_one_apply],
    calc bind₁ _ (witt_polynomial p ℤ k) = bind₁ X (witt_polynomial p ℤ k) : _
    ... = witt_polynomial p ℤ k : by simp only [bind₁_X_left, alg_hom.id_apply],
    apply eval₂_hom_congr' (ring_hom.ext_int _ _) _ rfl,
    rintro i hi -,
    rw [witt_polynomial_vars, finset.mem_range] at hi,
    dsimp, rw [if_pos], linarith }
end

end

end witt_vector
