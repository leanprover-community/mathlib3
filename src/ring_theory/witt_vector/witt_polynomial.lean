/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import data.mv_polynomial
import algebra.invertible

import ring_theory.witt_vector.witt_vector_preps

open mv_polynomial
open set
open finset (range)
open finsupp (single)

open_locale big_operators

local attribute [-simp] coe_eval₂_hom

variables (p : ℕ)
variables (R : Type*) [comm_ring R]

/-!
# Witt polynomials

To endow `witt_vector p R` with a ring structure,
we need to study the so-called Witt polynomials.

Fix a base value `p : ℕ`.
The `p`-adic Witt polynomials over are an infinite family of polynomials
indexed by a natural number `n`, taking values in an arbitrary ring `R`.
The variables of these polynomials are represented by natual numbers.
The `n`th Witt polynomial has at most `n+1` variables `X₀, ..., Xₙ`,
with exactly these variables when `R` has characteristic 0.

These polynomials are used to define the addition and multiplication operators
on the type of Witt vectors. (While this type itself is not complicated,
the ring operations are what make it interesting.)

When the base `p` is invertible in `R`, the `p`-adic Witt polynomials
form a basis for `mv_polynomial ℕ R`, equivalent to the standard basis.

We use the notation `W n` (and `W_ R n` when the ring needs to be explicit)
to represent the `n`th Witt polynomial.
-/


/-- `witt_polynomial p R n` is the `n`-th Witt polynomial
with respect to a prime `p` with coefficients in a commutative ring `R`.
It is defined as:

`∑_{i ≤ n} p^i X_i^{p^{n-i}} ∈ R[X_0, X_1, X_2, …]`. -/
noncomputable def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
∑ i in range (n+1), monomial (single i (p ^ (n - i))) (p ^ i)

lemma witt_polynomial_eq_sum_C_mul_X_pow (n : ℕ) :
  witt_polynomial p R n = ∑ i in range (n+1), C (p ^ i : R) * X i ^ (p ^ (n - i)) :=
begin
  apply finset.sum_congr rfl,
  rintro i -,
  rw [monomial_eq, finsupp.prod_single_index],
  rw pow_zero,
end

/-! We set up notation locally to this file, to keep statements short and comprehensible.
This allows us to simply write `W n` or `W_ ℤ n`. -/

-- Notation with ring of coefficients explicit
localized "notation `W_` := witt_polynomial p"   in witt
-- Notation with ring of coefficients implicit
localized "notation `W`  := witt_polynomial p _" in witt

open_locale witt
open mv_polynomial
/- The first observation is that the Witt polynomial doesn't really depend on the coefficient ring.
If we map the coefficients through a ring homomorphism, we obtain the corresponding Witt polynomial
over the target ring. -/
section
variables {R} {S : Type*} [comm_ring S]

@[simp] lemma map_witt_polynomial (f : R →+* S) (n : ℕ) :
  map f (W n) = W n :=
begin
  rw [witt_polynomial, ring_hom.map_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [map_monomial, ring_hom.map_pow, ring_hom.map_nat_cast],
end

variables (R)

@[simp] lemma constant_coeff_witt_polynomial [hp : fact p.prime] (n : ℕ) :
  constant_coeff (witt_polynomial p R n) = 0 :=
begin
  simp only [witt_polynomial, ring_hom.map_sum, constant_coeff_monomial],
  rw [finset.sum_eq_zero],
  rintro i hi,
  rw [if_neg],
  rw [finsupp.single_eq_zero],
  apply ne_of_gt,
  apply pow_pos hp.pos
end

@[simp] lemma witt_polynomial_zero : witt_polynomial p R 0 = X 0 :=
by simp only [witt_polynomial, X, finset.sum_singleton, finset.range_one, nat.pow_zero, pow_zero]

@[simp] lemma witt_polynomial_one : witt_polynomial p R 1 = C ↑p * X 1 + (X 0) ^ p :=
by simp only [witt_polynomial_eq_sum_C_mul_X_pow, finset.sum_range_succ, finset.range_one,
    finset.sum_singleton, one_mul, pow_one, nat.pow_zero, C_1, pow_zero, nat.pow_one]

lemma aeval_witt_polynomial {A : Type*} [comm_ring A] [algebra R A] (f : ℕ → A) (n : ℕ) :
  aeval f (W_ R n) = ∑ i in range (n+1), p^i * (f i) ^ (p ^ (n-i)) :=
by simp [witt_polynomial, alg_hom.map_sum, aeval_monomial, finsupp.prod_single_index]

/--
Over the ring `zmod (p^(n+1))`, we produce the `n+1`st Witt polynomial
by expanding the `n`th witt polynomial by `p`.
-/
@[simp] lemma witt_polynomial_zmod_self (n : ℕ) :
  W_ (zmod (p ^ (n + 1))) (n + 1) = expand p (W_ (zmod (p^(n + 1))) n) :=
begin
  simp only [witt_polynomial_eq_sum_C_mul_X_pow],
  rw [finset.sum_range_succ, ← nat.cast_pow, char_p.cast_eq_zero (zmod (p^(n+1))) (p^(n+1)),
      C_0, zero_mul, zero_add],
  rw [alg_hom.map_sum, finset.sum_congr rfl],
  intros k hk,
  rw [alg_hom.map_mul, alg_hom.map_pow, expand_X, alg_hom_C, ← pow_mul, ← pow_succ],
  congr,
  rw finset.mem_range at hk,
  omega
end

section p_prime
-- in fact, `0 < p` would be sufficient
variables [hp : fact p.prime]
include hp

lemma witt_polynomial_vars [char_zero R] (n : ℕ) :
  (witt_polynomial p R n).vars = finset.range (n + 1) :=
begin
  have : ∀ i, (monomial (finsupp.single i (p ^ (n - i))) (p ^ i : R)).vars = {i},
  { intro i,
    rw vars_monomial_single,
    { rw ← nat.pos_iff_ne_zero,
      apply nat.pow_pos hp.pos },
    { rw [← nat.cast_pow, nat.cast_ne_zero],
      apply ne_of_gt,
      apply pow_pos hp.pos i } },
  rw [witt_polynomial, vars_sum_of_disjoint],
  { simp only [this, int.nat_cast_eq_coe_nat, finset.bind_singleton_eq_self], },
  { simp only [this, int.nat_cast_eq_coe_nat],
    intros a b h,
    apply finset.singleton_disjoint.mpr,
    rwa finset.mem_singleton, },
end

lemma witt_polynomial_vars_subset (n : ℕ) :
  (witt_polynomial p R n).vars ⊆ finset.range (n + 1) :=
begin
  rw [← map_witt_polynomial p (int.cast_ring_hom R), ← witt_polynomial_vars p ℤ],
  apply vars_map,
end

end p_prime

end

/-!

## Witt polynomials as a basis

-/

-- We need p to be invertible for the following definitions

/-- The `X_in_terms_of_W p R n` is the polynomial on the basis of Witt polynomials
that corresponds to the ordinary `X n`. -/
noncomputable def X_in_terms_of_W [invertible (p : R)] :
  ℕ → mv_polynomial ℕ R
| n := (X n - (∑ i : fin n,
  have _ := i.2, (C (p^(i : ℕ) : R) * (X_in_terms_of_W i)^(p^(n-i))))) * C (⅟p ^ n : R)

lemma X_in_terms_of_W_eq [invertible (p : R)] {n : ℕ} :
  X_in_terms_of_W p R n =
  (X n - (∑ i in range n, C (p^i : R) * X_in_terms_of_W p R i ^ p ^ (n - i))) * C (⅟p ^ n : R) :=
by { rw [X_in_terms_of_W, ← fin.sum_univ_eq_sum_range], refl }

@[simp] lemma constant_coeff_X_in_terms_of_W [hp : fact p.prime] [invertible (p : R)] (n : ℕ) :
  constant_coeff (X_in_terms_of_W p R n) = 0 :=
begin
  apply nat.strong_induction_on n; clear n,
  intros n IH,
  rw [X_in_terms_of_W_eq, mul_comm, ring_hom.map_mul, ring_hom.map_sub, ring_hom.map_sum,
    constant_coeff_C, finset.sum_eq_zero],
  { simp only [constant_coeff_X, sub_zero, mul_zero] },
  { intros m H,
    rw finset.mem_range at H,
    simp only [ring_hom.map_mul, ring_hom.map_pow, constant_coeff_C, IH m H],
    rw [zero_pow, mul_zero],
    apply nat.pow_pos hp.pos, }
end

@[simp] lemma X_in_terms_of_W_zero [invertible (p : R)] :
  X_in_terms_of_W p R 0 = X 0 :=
by rw [X_in_terms_of_W_eq, finset.range_zero, finset.sum_empty, pow_zero, C_1, mul_one, sub_zero]

section p_prime
variables [hp : fact p.prime]
include hp

-- shouldn't this be a global instance?
local attribute [instance] invertible_inv_of

lemma X_in_terms_of_W_vars_aux (n : ℕ) :
  n ∈ (X_in_terms_of_W p ℚ n).vars ∧
  (X_in_terms_of_W p ℚ n).vars ⊆ finset.range (n + 1) :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n ih,
  -- TODO: change `vars_X` to use `nontrivial` instead of `0 ≠ 1`
  rw [X_in_terms_of_W_eq, mul_comm, vars_C_mul, vars_sub_of_disjoint, vars_X zero_ne_one,
      finset.range_succ, finset.insert_eq],
  { simp only [true_and, true_or, eq_self_iff_true,
      finset.mem_union, finset.mem_singleton],
    intro i,
    rw [finset.mem_union, finset.mem_union],
    apply or.imp id,
    intro hi,
    replace hi := vars_sum_subset _ _ hi,
    rw finset.mem_bind at hi,
    rcases hi with ⟨j, hj, hi⟩,
    rw vars_C_mul at hi,
    swap,
    { apply pow_ne_zero, exact_mod_cast hp.ne_zero },
    rw finset.mem_range at hj,
    replace hi := (ih j hj).2 (vars_pow _ _ hi),
    rw finset.mem_range at hi ⊢,
    exact lt_of_lt_of_le hi hj },
  { apply_instance },
  { rw [vars_X zero_ne_one, finset.singleton_disjoint],
    swap, apply_instance,
    -- the duplication, aaahrg
    intro H,
    replace H := vars_sum_subset _ _ H,
    rw finset.mem_bind at H,
    rcases H with ⟨j, hj, H⟩,
    rw vars_C_mul at H,
    swap,
    { apply pow_ne_zero, exact_mod_cast hp.ne_zero },
    rw finset.mem_range at hj,
    replace H := (ih j hj).2 (vars_pow _ _ H),
    rw finset.mem_range at H,
    exact lt_irrefl n (lt_of_lt_of_le H hj) },
  { apply nonzero_of_invertible, }
end

lemma X_in_terms_of_W_vars_subset (n : ℕ) :
  (X_in_terms_of_W p ℚ n).vars ⊆ finset.range (n + 1) :=
(X_in_terms_of_W_vars_aux p n).2

end p_prime

lemma X_in_terms_of_W_aux [invertible (p : R)] (n : ℕ) :
  X_in_terms_of_W p R n * C (p^n : R) =
  X n - ∑ i in range n, C (p^i : R) * (X_in_terms_of_W p R i)^p^(n-i) :=
by rw [X_in_terms_of_W_eq, mul_assoc, ← C_mul, ← mul_pow, inv_of_mul_self, one_pow, C_1, mul_one]

@[simp] lemma bind₁_X_in_terms_of_W_witt_polynomial [invertible (p : R)] (k : ℕ) :
  bind₁ (X_in_terms_of_W p R) (W_ R k) = X k :=
begin
  rw [witt_polynomial_eq_sum_C_mul_X_pow, alg_hom.map_sum],
  simp only [alg_hom.map_pow, C_pow, alg_hom.map_mul, alg_hom_C],
  rw [finset.sum_range_succ, nat.sub_self, nat.pow_zero, pow_one, bind₁_X_right,
      mul_comm, ← C_pow, X_in_terms_of_W_aux],
  simp only [C_pow, bind₁_X_right, sub_add_cancel],
end

@[simp] lemma bind₁_witt_polynomial_X_in_terms_of_W [invertible (p : R)] (n : ℕ) :
  bind₁ (W_ R) (X_in_terms_of_W p R n) = X n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq, alg_hom.map_mul, alg_hom.map_sub, bind₁_X_right, alg_hom_C, alg_hom.map_sum],
  have : W_ R n - ∑ i in range n, C (p ^ i : R) * (X i) ^ p ^ (n - i) = C (p ^ n : R) * X n,
  by simp only [witt_polynomial_eq_sum_C_mul_X_pow, nat.sub_self, finset.sum_range_succ,
    pow_one, add_sub_cancel, nat.pow_zero],
  rw [finset.sum_congr rfl, this],
  { -- this is really slow for some reason
    rw [mul_right_comm, ← C_mul, ← mul_pow, mul_inv_of_self, one_pow, C_1, one_mul], },
  { intros i h,
    rw finset.mem_range at h,
    simp only [alg_hom.map_mul, alg_hom.map_pow, alg_hom_C, H i h] },
end

/--
The Witt polynomials induce an algebra equivalence from `mv_polynomial ℕ R` to itself,
under the assumption that `p` is invertible in `R`.
-/
noncomputable def witt.alg_equiv [invertible (p : R)] : mv_polynomial ℕ R ≃ₐ[R] mv_polynomial ℕ R :=
equiv_of_family (W_ R) (X_in_terms_of_W p R)
(bind₁_X_in_terms_of_W_witt_polynomial p R)
(bind₁_witt_polynomial_X_in_terms_of_W p R)
