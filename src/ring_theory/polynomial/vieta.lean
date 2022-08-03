/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.polynomial.basic
import ring_theory.polynomial.symmetric

/-!
# Vieta's Formula

The main result is `multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms ` X + λ` with `λ` in a `multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `mv_polynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

-/

open_locale big_operators polynomial

namespace multiset

section semiring

variables {R : Type*} [comm_semiring R]

/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
lemma prod_X_add_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ r, polynomial.X + polynomial.C r)).prod =
  ∑ j in finset.range (s.card + 1), (polynomial.C (s.esymm j) * polynomial.X^(s.card - j)) :=
begin
  classical,
  rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ←sum_powerset_len, function.comp,
    finset.sum_eq_multiset_sum, finset.sum_eq_multiset_sum, ←join, ←bind, map_bind, sum_bind],
  rw map_congr (eq.refl _),
  intros _ _,
  rw [esymm, ←sum_hom', ←sum_map_mul_right, map_congr (eq.refl _)],
  intros _ ht,
  rw mem_powerset_len at ht,
  simp [ht, map_const, prod_repeat, prod_hom', map_id', card_sub],
end

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
lemma prod_X_add_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
  polynomial.coeff (s.map (λ r, polynomial.X + polynomial.C r)).prod k =
    s.esymm (s.card - k) :=
begin
  convert polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k,
  simp_rw [polynomial.finset_sum_coeff, polynomial.coeff_C_mul_X_pow],
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

end semiring

section ring

variables  {R : Type*} [comm_ring R]

lemma esymm_neg (s : multiset R) (k : ℕ) :
  (map has_neg.neg s).esymm k = (-1)^k * esymm s k :=
begin
  rw [esymm, esymm, ←multiset.sum_map_mul_left, multiset.powerset_len_map, multiset.map_map],
  rw map_congr (eq.refl _),
  intros x hx,
  rw [(by { exact (mem_powerset_len.mp hx).right.symm }), ←prod_repeat, ←multiset.map_const],
  nth_rewrite 2 ←map_id' x,
  rw [←prod_map_mul, map_congr (eq.refl _)],
  exact λ z _, neg_one_mul z,
end

lemma prod_X_sub_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ t, polynomial.X - polynomial.C t)).prod =
  ∑ j in finset.range (s.card + 1),
  (-1)^j* (polynomial.C (s.esymm j) * polynomial.X ^ (s.card - j)) :=
begin
  conv_lhs { congr, congr, funext, rw sub_eq_add_neg, rw ←map_neg polynomial.C _, },
  convert prod_X_add_C_eq_sum_esymm (map (λ t, -t) s) using 1,
  { rwa map_map, },
  { simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one], },
end

lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
  polynomial.coeff (s.map (λ t, polynomial.X - polynomial.C t)).prod k =
    (-1)^(s.card - k) * s.esymm (s.card - k) :=
begin
  conv_lhs { congr, congr, congr, funext, rw sub_eq_add_neg, rw ←map_neg polynomial.C _, },
  convert prod_X_add_C_coeff (map (λ t, -t) s) _ using 1,
  { rwa map_map, },
  { rwa [esymm_neg, card_map] },
  { rwa card_map },
end

end ring

end multiset

namespace mv_polynomial

open finset polynomial fintype

variables (R σ : Type*) [comm_semiring R] [fintype σ]

/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma prod_C_add_X_eq_sum_esymm :
  (∏ i : σ, (polynomial.X + polynomial.C (X i)) : polynomial (mv_polynomial σ R) )=
  ∑ j in range (card σ + 1),
    (polynomial.C (esymm σ R j) * polynomial.X ^ (card σ - j)) :=
begin
  let s := (multiset.map (λ i : σ, (X i : mv_polynomial σ R)) finset.univ.val),
  rw (_ : card σ = s.card),
  { simp_rw [esymm_eq_multiset.esymm σ R _, finset.prod_eq_multiset_prod],
    convert multiset.prod_X_add_C_eq_sum_esymm s,
    rwa multiset.map_map, },
  { rw multiset.card_map, exact rfl, }
end

lemma prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ):
  (∏ i : σ, (polynomial.X + polynomial.C (X i)) : polynomial (mv_polynomial σ R) ).coeff k =
  esymm σ R (card σ - k) :=
begin
  let s := (multiset.map (λ i : σ, (X i : mv_polynomial σ R)) finset.univ.val),
  rw (_ : card σ = s.card) at ⊢ h,
  { rw [esymm_eq_multiset.esymm σ R (s.card - k), finset.prod_eq_multiset_prod],
    convert multiset.prod_X_add_C_coeff s h,
    rwa multiset.map_map },
  repeat { rw multiset.card_map, exact rfl, },
end

end mv_polynomial
