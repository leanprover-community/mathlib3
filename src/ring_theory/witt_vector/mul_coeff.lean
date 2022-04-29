/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/

import ring_theory.witt_vector.truncated
import data.mv_polynomial.supported

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `mv_polynomial (fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `witt_vector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/

noncomputable theory

namespace witt_vector

variables (p : ℕ) [hp : fact p.prime]
variables {k : Type*} [comm_ring k]
local notation `𝕎` := witt_vector p
open finset mv_polynomial
open_locale big_operators

/--
```
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
  (∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
def witt_poly_prod (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n) *
  rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n)

include hp

lemma witt_poly_prod_vars (n : ℕ) :
  (witt_poly_prod p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw [witt_poly_prod],
  apply subset.trans (vars_mul _ _),
  apply union_subset;
  { apply subset.trans (vars_rename _ _),
    simp [witt_polynomial_vars,image_subset_iff] }
end

/-- The "remainder term" of `witt_vector.witt_poly_prod`. See `mul_poly_of_interest_aux2`. -/
def witt_poly_prod_remainder (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
∑ i in range n, p^i * (witt_mul p i)^(p^(n-i))

lemma witt_poly_prod_remainder_vars (n : ℕ) :
  (witt_poly_prod_remainder p n).vars ⊆ finset.univ.product (finset.range n) :=
begin
  rw [witt_poly_prod_remainder],
  apply subset.trans (vars_sum_subset _ _),
  rw bUnion_subset,
  intros x hx,
  apply subset.trans (vars_mul _ _),
  apply union_subset,
  { apply subset.trans (vars_pow _ _),
    have : (p : mv_polynomial (fin 2 × ℕ) ℤ) = (C (p : ℤ)),
    { simp only [int.cast_coe_nat, ring_hom.eq_int_cast] },
    rw [this, vars_C],
    apply empty_subset },
  { apply subset.trans (vars_pow _ _),
    apply subset.trans (witt_mul_vars _ _),
    apply product_subset_product (subset.refl _),
    simp only [mem_range, range_subset] at hx ⊢,
    exact hx }
end

omit hp

/--
`remainder p n` represents the remainder term from `mul_poly_of_interest_aux3`.
`witt_poly_prod p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
def remainder (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
(∑ (x : ℕ) in
     range (n + 1),
     (rename (prod.mk 0)) ((monomial (finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))) *
  ∑ (x : ℕ) in
    range (n + 1),
    (rename (prod.mk 1)) ((monomial (finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))

include hp

lemma remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ.product (range (n+1)) :=
begin
  rw [remainder],
  apply subset.trans (vars_mul _ _),
  apply union_subset;
  { apply subset.trans (vars_sum_subset _ _),
    rw bUnion_subset,
    intros x hx,
    rw [rename_monomial, vars_monomial, finsupp.map_domain_single],
    { apply subset.trans (finsupp.support_single_subset),
      simp [hx], },
    { apply pow_ne_zero,
      exact_mod_cast hp.out.ne_zero } }
end

/-- This is the polynomial whose degree we want to get a handle on. -/
def poly_of_interest (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
witt_mul p (n + 1) + p^(n+1) * X (0, n+1) * X (1, n+1) -
  (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) -
  (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1))

lemma mul_poly_of_interest_aux1 (n : ℕ) :
  (∑ i in range (n+1), p^i * (witt_mul p i)^(p^(n-i)) : mv_polynomial (fin 2 × ℕ) ℤ) =
    witt_poly_prod p n :=
begin
  simp only [witt_poly_prod],
  convert witt_structure_int_prop p (X (0 : fin 2) * X 1) n using 1,
  { simp only [witt_polynomial, witt_mul, int.nat_cast_eq_coe_nat],
    rw alg_hom.map_sum,
    congr' 1 with i,
    congr' 1,
    have hsupp : (finsupp.single i (p ^ (n - i))).support = {i},
    { rw finsupp.support_eq_singleton,
      simp only [and_true, finsupp.single_eq_same, eq_self_iff_true, ne.def],
      exact pow_ne_zero _ hp.out.ne_zero, },
    simp only [bind₁_monomial, hsupp, int.cast_coe_nat, prod_singleton, ring_hom.eq_int_cast,
      finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, true_or, eq_self_iff_true], },
  { simp only [map_mul, bind₁_X_right] }
end

lemma mul_poly_of_interest_aux2 (n : ℕ) :
  (p ^ n * witt_mul p n : mv_polynomial (fin 2 × ℕ) ℤ) + witt_poly_prod_remainder p n =
    witt_poly_prod p n :=
begin
  convert mul_poly_of_interest_aux1 p n,
  rw [sum_range_succ, add_comm, nat.sub_self, pow_zero, pow_one],
  refl
end

omit hp
lemma mul_poly_of_interest_aux3 (n : ℕ) :
  witt_poly_prod p (n+1) =
  - (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  remainder p n :=
begin
  -- a useful auxiliary fact
  have mvpz : (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) = mv_polynomial.C (↑p ^ (n + 1)),
  { simp only [int.cast_coe_nat, ring_hom.eq_int_cast, C_pow, eq_self_iff_true] },

  -- unfold definitions and peel off the last entries of the sums.
  rw [witt_poly_prod, witt_polynomial, alg_hom.map_sum, alg_hom.map_sum,
      sum_range_succ],
  -- these are sums up to `n+2`, so be careful to only unfold to `n+1`.
  conv_lhs {congr, skip, rw [sum_range_succ] },
  simp only [add_mul, mul_add, tsub_self, int.nat_cast_eq_coe_nat, pow_zero, alg_hom.map_sum],

  -- rearrange so that the first summand on rhs and lhs is `remainder`, and peel off
  conv_rhs { rw add_comm },
  simp only [add_assoc],
  apply congr_arg (has_add.add _),
  conv_rhs { rw sum_range_succ },

  -- the rest is equal with proper unfolding and `ring`
  simp only [rename_monomial, monomial_eq_C_mul_X, map_mul, rename_C, pow_one, rename_X, mvpz],
  simp only [int.cast_coe_nat, map_pow, ring_hom.eq_int_cast, rename_X, pow_one, tsub_self,
    pow_zero],
  ring,
end
include hp

lemma mul_poly_of_interest_aux4 (n : ℕ) :
  (p ^ (n + 1) * witt_mul p (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) =
  - (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (remainder p n - witt_poly_prod_remainder p (n + 1)) :=
begin
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_poly_of_interest_aux2],
  exact mul_poly_of_interest_aux3 _ _
end

lemma mul_poly_of_interest_aux5 (n : ℕ) :
  (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) *
    poly_of_interest p n =
  (remainder p n - witt_poly_prod_remainder p (n + 1)) :=
begin
  simp only [poly_of_interest, mul_sub, mul_add, sub_eq_iff_eq_add'],
  rw mul_poly_of_interest_aux4 p n,
  ring,
end

lemma mul_poly_of_interest_vars (n : ℕ) :
  ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * poly_of_interest p n).vars ⊆
  univ.product (range (n+1)) :=
begin
  rw mul_poly_of_interest_aux5,
  apply subset.trans (vars_sub_subset _ _),
  apply union_subset,
  { apply remainder_vars },
  { apply witt_poly_prod_remainder_vars }
end

lemma poly_of_interest_vars_eq (n : ℕ) :
  (poly_of_interest p n).vars =
    ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * (witt_mul p (n + 1) +
    p^(n+1) * X (0, n+1) * X (1, n+1) -
    (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) -
    (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)))).vars :=
begin
  have : (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) = C (p ^ (n + 1) : ℤ),
  { simp only [int.cast_coe_nat, ring_hom.eq_int_cast, C_pow, eq_self_iff_true] },
  rw [poly_of_interest, this, vars_C_mul],
  apply pow_ne_zero,
  exact_mod_cast hp.out.ne_zero
end

lemma poly_of_interest_vars (n : ℕ) : (poly_of_interest p n).vars ⊆ univ.product (range (n+1)) :=
by rw poly_of_interest_vars_eq; apply mul_poly_of_interest_vars

lemma peval_poly_of_interest (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) + p^(n+1) * x.coeff (n+1) * y.coeff (n+1)
    - y.coeff (n+1) * ∑ i in range (n+1+1), p^i * x.coeff i ^ (p^(n+1-i))
    - x.coeff (n+1) * ∑ i in range (n+1+1), p^i * y.coeff i ^ (p^(n+1-i)) :=
begin
  simp only [poly_of_interest, peval, map_nat_cast, matrix.head_cons, map_pow,
    function.uncurry_apply_pair, aeval_X,
  matrix.cons_val_one, map_mul, matrix.cons_val_zero, map_sub],
  rw [sub_sub, add_comm (_ * _), ← sub_sub],
  have mvpz : (p : mv_polynomial ℕ ℤ) = mv_polynomial.C ↑p,
  { rw [ring_hom.eq_int_cast, int.cast_coe_nat] },
  congr' 3,
  { simp only [mul_coeff, peval, map_nat_cast, map_add, matrix.head_cons, map_pow,
      function.uncurry_apply_pair, aeval_X, matrix.cons_val_one, map_mul, matrix.cons_val_zero], },
  all_goals
  { simp only [witt_polynomial_eq_sum_C_mul_X_pow, aeval, eval₂_rename, int.cast_coe_nat,
      ring_hom.eq_int_cast, eval₂_mul, function.uncurry_apply_pair, function.comp_app, eval₂_sum,
      eval₂_X, matrix.cons_val_zero, eval₂_pow, int.cast_pow, ring_hom.to_fun_eq_coe, coe_eval₂_hom,
      int.nat_cast_eq_coe_nat, alg_hom.coe_mk],
  congr' 1 with z,
  rw [mvpz, mv_polynomial.eval₂_C],
  refl }
end

variable [char_p k p]

/-- The characteristic `p` version of `peval_poly_of_interest` -/
lemma peval_poly_of_interest' (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) - y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    - x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) :=
begin
  rw peval_poly_of_interest,
  have : (p : k) = 0 := char_p.cast_eq_zero (k) p,
  simp only [this, add_zero, zero_mul, nat.succ_ne_zero, ne.def, not_false_iff, zero_pow'],
  have sum_zero_pow_mul_pow_p : ∀ y : 𝕎 k,
    ∑ (x : ℕ) in range (n + 1 + 1), 0 ^ x * y.coeff x ^ p ^ (n + 1 - x) = y.coeff 0 ^ p ^ (n + 1),
  { intro y,
    rw finset.sum_eq_single_of_mem 0,
    { simp },
    { simp },
    { intros j _ hj,
      simp [zero_pow (zero_lt_iff.mpr hj)] } },
  congr; apply sum_zero_pow_mul_pow_p,
end

variable (k)
lemma nth_mul_coeff' (n : ℕ) :
  ∃ f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k, ∀ (x y : 𝕎 k),
  f (truncate_fun (n+1) x) (truncate_fun (n+1) y)
  = (x * y).coeff (n+1) - y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    - x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) :=
begin
  simp only [←peval_poly_of_interest'],
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars k (poly_of_interest_vars p n),
  let f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k,
  { intros x y,
    apply f₀,
    rintros ⟨a, ha⟩,
    apply function.uncurry (![x, y]),
    simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
       multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
    refine ⟨a.fst, ⟨a.snd, _⟩⟩,
    cases ha with ha ha; linarith only [ha] },
  use f,
  intros x y,
  dsimp [peval],
  rw ← hf₀,
  simp only [f, function.uncurry_apply_pair],
  congr,
  ext a,
  cases a with a ha,
  cases a with i m,
  simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
    multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
  have ha' : m < n + 1 := by cases ha with ha ha; linarith only [ha],
  fin_cases i;  -- surely this case split is not necessary
  { simpa only using x.coeff_truncate_fun ⟨m, ha'⟩ }
end

lemma nth_mul_coeff (n : ℕ) :
  ∃ f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k, ∀ (x y : 𝕎 k),
    (x * y).coeff (n+1) =
      x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1)) +
      f (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
begin
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n,
  use f,
  intros x y,
  rw hf x y,
  ring,
end

variable {k}

/--
Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
def nth_remainder (n : ℕ) : (fin (n+1) → k) → (fin (n+1) → k) → k :=
classical.some (nth_mul_coeff p k n)

lemma nth_remainder_spec (n : ℕ) (x y : 𝕎 k) :
  (x * y).coeff (n+1) =
    x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1)) +
    nth_remainder p n (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
classical.some_spec (nth_mul_coeff p k n) _ _

end witt_vector
