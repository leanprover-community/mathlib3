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
  simp only [init, select, coeff_mk],
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

noncomputable theory

section

local attribute [semireducible] witt_vector

/-- `witt_vector.select P x`, for a (decidable) predicate `P : ℕ → Prop` is the Witt vector
whose `n`-th coefficient is `x.coeff n` if `P n` is true, and `0` otherwise.
-/
def select (P : ℕ → Prop) [decidable_pred P] (x : 𝕎 R) : 𝕎 R :=
mk p (λ k, if P k then x.coeff k else 0)

section select
variables (P : ℕ → Prop) [decidable_pred P]

def select_poly (k : ℕ) : mv_polynomial ℕ ℤ := if P k then X k else 0

def select_is_poly : is_poly p (λ R _Rcr x, by exactI select P x) (select_poly P) :=
{ coeff :=
  begin
    rintro R _Rcr x,
    funext i,
    dsimp [select, select_poly],
    split_ifs with hi,
    { rw [aeval_X] },
    { rw [alg_hom.map_zero] }
  end }

end select

/-- `witt_vector.init x n` is the Witt vector of which the first `n` coefficients are those from `x`
and all other coefficients are `0`.
See `witt_vector.tail` for the complementary part.
-/
def init (x : 𝕎 R) (n : ℕ) : 𝕎 R := select (λ i, i < n) x

/-- `witt_vector.tail x n` is the Witt vector of which the first `n` coefficients are `0`
and all other coefficients are those from `x`.
See `witt_vector.init` for the complementary part. -/
def tail (x : 𝕎 R) (n : ℕ) : 𝕎 R := select (λ i, n ≤ i) x

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
def init_is_poly (n : ℕ) : is_poly p (λ R _Rcr x, by exactI init x n) _ :=
select_is_poly (λ i, i < n)

end

end witt_vector
