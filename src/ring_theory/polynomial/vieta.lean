/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import data.polynomial.splits
import ring_theory.mv_polynomial.symmetric

/-!
# Vieta's Formula

The main result is `multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `mv_polynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/

open_locale big_operators polynomial

namespace multiset

open polynomial

section semiring

variables {R : Type*} [comm_semiring R]

/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
lemma prod_X_add_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ r, X + C r)).prod =
  ∑ j in finset.range (s.card + 1), C (s.esymm j) * X ^ (s.card - j) :=
begin
  classical,
  rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ←bind_powerset_len, function.comp,
    map_bind, sum_bind, finset.sum_eq_multiset_sum, finset.range_val, map_congr (eq.refl _)],
  intros _ _,
  rw [esymm, ←sum_hom', ←sum_map_mul_right, map_congr (eq.refl _)],
  intros _ ht,
  rw mem_powerset_len at ht,
  simp [ht, map_const, prod_replicate, prod_hom', map_id', card_sub],
end

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
lemma prod_X_add_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card) :
  (s.map (λ r, X + C r)).prod.coeff k = s.esymm (s.card - k) :=
begin
  convert polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k,
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow],
  rw finset.sum_eq_single_of_mem (s.card - k) _,
  { rw if_pos (nat.sub_sub_self h).symm, },
  { intros j hj1 hj2,
    suffices : k ≠ card s - j,
    { rw if_neg this, },
    { intro hn,
      rw [hn, nat.sub_sub_self (nat.lt_succ_iff.mp (finset.mem_range.mp hj1))] at hj2,
      exact ne.irrefl hj2, }},
  { rw finset.mem_range,
    exact nat.sub_lt_succ s.card k }
end

lemma prod_X_add_C_coeff' {σ} (s : multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
  (s.map (λ i, X + C (r i))).prod.coeff k = (s.map r).esymm (s.card - k) :=
by rw [← map_map (λ r, X + C r) r, prod_X_add_C_coeff]; rwa s.card_map r

lemma _root_.finset.prod_X_add_C_coeff {σ} (s : finset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
  (∏ i in s, (X + C (r i))).coeff k = ∑ t in s.powerset_len (s.card - k), ∏ i in t, r i :=
by { rw [finset.prod, prod_X_add_C_coeff' _ r h, finset.esymm_map_val], refl }

end semiring

section ring

variables {R : Type*} [comm_ring R]

lemma esymm_neg (s : multiset R) (k : ℕ) :
  (map has_neg.neg s).esymm k = (-1) ^ k * esymm s k :=
begin
  rw [esymm, esymm, ←multiset.sum_map_mul_left, multiset.powerset_len_map, multiset.map_map,
    map_congr (eq.refl _)],
  intros x hx,
  rw [(by { exact (mem_powerset_len.mp hx).right.symm }), ←prod_replicate, ←multiset.map_const],
  nth_rewrite 2 ←map_id' x,
  rw [←prod_map_mul, map_congr (eq.refl _)],
  exact λ z _, neg_one_mul z,
end

lemma prod_X_sub_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ t, X - C t)).prod =
  ∑ j in finset.range (s.card + 1), (-1) ^ j * (C (s.esymm j) * X ^ (s.card - j)) :=
begin
  conv_lhs { congr, congr, funext, rw sub_eq_add_neg, rw ←map_neg C _, },
  convert prod_X_add_C_eq_sum_esymm (map (λ t, -t) s) using 1,
  { rwa map_map, },
  { simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one], },
end

lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card) :
  (s.map (λ t, X - C t)).prod.coeff k = (-1) ^ (s.card - k) * s.esymm (s.card - k) :=
begin
  conv_lhs { congr, congr, congr, funext, rw sub_eq_add_neg, rw ←map_neg C _, },
  convert prod_X_add_C_coeff (map (λ t, -t) s) _ using 1,
  { rwa map_map, },
  { rwa [esymm_neg, card_map] },
  { rwa card_map },
end

/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
theorem _root_.polynomial.coeff_eq_esymm_roots_of_card [is_domain R] {p : R[X]}
  (hroots : p.roots.card = p.nat_degree) {k : ℕ} (h : k ≤ p.nat_degree) :
  p.coeff k = p.leading_coeff * (-1) ^ (p.nat_degree - k) * p.roots.esymm (p.nat_degree - k) :=
begin
  conv_lhs { rw ← C_leading_coeff_mul_prod_multiset_X_sub_C hroots },
  rw [coeff_C_mul, mul_assoc], congr,
  convert p.roots.prod_X_sub_C_coeff _ using 3; rw hroots, exact h,
end

/-- Vieta's formula for split polynomials over a field. -/
theorem _root_.polynomial.coeff_eq_esymm_roots_of_splits {F} [field F] {p : F[X]}
  (hsplit : p.splits (ring_hom.id F)) {k : ℕ} (h : k ≤ p.nat_degree) :
  p.coeff k = p.leading_coeff * (-1) ^ (p.nat_degree - k) * p.roots.esymm (p.nat_degree - k) :=
polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

end ring

end multiset

section mv_polynomial

open finset polynomial fintype

variables (R σ : Type*) [comm_semiring R] [fintype σ]

/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma mv_polynomial.prod_C_add_X_eq_sum_esymm :
  ∏ i : σ, (X + C (mv_polynomial.X i)) =
  ∑ j in range (card σ + 1), (C (mv_polynomial.esymm σ R j) * X ^ (card σ - j)) :=
begin
  let s := finset.univ.val.map (λ i : σ, mv_polynomial.X i),
  rw (_ : card σ = s.card),
  { simp_rw [mv_polynomial.esymm_eq_multiset_esymm σ R, finset.prod_eq_multiset_prod],
    convert multiset.prod_X_add_C_eq_sum_esymm s,
    rwa multiset.map_map, },
  { rw multiset.card_map, refl, }
end

lemma mv_polynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
  (∏ i : σ, (X + C (mv_polynomial.X i))).coeff k = mv_polynomial.esymm σ R (card σ - k) :=
begin
  let s := finset.univ.val.map (λ i, (mv_polynomial.X i : mv_polynomial σ R)),
  rw (_ : card σ = s.card) at ⊢ h,
  { rw [mv_polynomial.esymm_eq_multiset_esymm σ R, finset.prod_eq_multiset_prod],
    convert multiset.prod_X_add_C_coeff s h,
    rwa multiset.map_map },
  repeat { rw multiset.card_map, refl, },
end

end mv_polynomial
