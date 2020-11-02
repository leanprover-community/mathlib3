/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/

import field_theory.splitting_field
import ring_theory.roots_of_unity
import algebra.polynomial.big_operators
import number_theory.divisors
import data.polynomial.lifts
import analysis.complex.roots_of_unity

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n`
with coefficients in `ℤ`, using `cyclotomic' n ℂ`.

## Main definition

* `cyclotomic n` : the `n`-th cyclotomic polynomial with coefficients in `ℤ`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `X_pow_sub_one_eq_prod_cycl` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. To get the standard
cyclotomic polynomials with integer coefficients, we use `int_coeff_of_cycl`, with `R = ℂ`, that is
the main example. We decided to work in general since the difficulties are essentially the same.

-/

open_locale classical big_operators
noncomputable theory

universes u v
variables {R : Type*} [integral_domain R]

namespace polynomial

section integral_domain

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type*) [integral_domain R] : polynomial R :=
∏ μ in primitive_roots n R, (X - C μ)

/- The zeroth modified cyclotomic polyomial is `1`. -/
lemma cyclotomic'_zero (R : Type*) [integral_domain R] : cyclotomic' 0 R = 1 :=
begin
  rw [cyclotomic'],
  have prim_root_zero : primitive_roots 0 R = ∅,
  { rw [← finset.val_eq_zero, ← multiset.subset_zero, ← nth_roots_zero (1 : R), primitive_roots],
    simp only [finset.not_mem_empty, forall_const, forall_prop_of_false, multiset.to_finset_zero,
    finset.filter_true_of_mem, finset.empty_val, not_false_iff,
    multiset.zero_subset, nth_roots_zero] },
  simp only [prim_root_zero, finset.prod_empty]
end

/- The first modified cyclotomic polyomial is `X - 1`. -/
lemma cyclotomic'_one (R : Type*) [integral_domain R] : cyclotomic' 1 R = X - 1 :=
begin
  rw [cyclotomic'],
  have prim_root_one : primitive_roots 1 R = {(1 : R)},
  { apply finset.eq_singleton_iff_unique_mem.2,
    split,
    { simp only [is_primitive_root.one_right_iff, mem_primitive_roots zero_lt_one] },
    { intros x hx,
      rw [mem_primitive_roots zero_lt_one, is_primitive_root.one_right_iff] at hx,
      exact hx } },
  simp only [prim_root_one, finset.prod_singleton, ring_hom.map_one]
end

/- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
lemma cyclotomic'_two (R : Type*) [integral_domain R] (p : ℕ) [char_p R p] (hp : p ≠ 2) :
  cyclotomic' 2 R = X + 1 :=
begin
  rw [cyclotomic'],
  have prim_root_two : primitive_roots 2 R = {(-1 : R)},
  { apply finset.eq_singleton_iff_unique_mem.2,
    split,
    { simp only [is_primitive_root.neg_one p hp, nat.succ_pos', mem_primitive_roots] },
    { intros x hx,
      rw [mem_primitive_roots zero_lt_two] at hx,
      exact is_primitive_root.eq_neg_one_of_two_right hx } },
  simp only [prim_root_two, finset.prod_singleton, ring_hom.map_neg, ring_hom.map_one,
  sub_neg_eq_add]
end

/-- `cyclotomic' n R` is monic. -/
lemma cyclotomic'.monic (n : ℕ) (R : Type*) [integral_domain R] : (cyclotomic' n R).monic :=
monic_prod_of_monic _ _ $ λ z hz, monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
lemma cycl'_ne_zero (n : ℕ) (R : Type*) [integral_domain R] : cyclotomic' n R ≠ 0 :=
  monic.ne_zero (cyclotomic'.monic n R)

/- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
lemma nat_deg_of_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).nat_degree = nat.totient n :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, cyclotomic'_zero, nat.totient_zero, nat_degree_one] },
  rw [cyclotomic'],
  rw nat_degree_prod (primitive_roots n R) (λ (z : R), (X - C z)),
  simp only [is_primitive_root.card_primitive_roots h (nat.pos_of_ne_zero hzero), mul_one,
  nat_degree_X_sub_C,
  nat.cast_id, finset.sum_const, nsmul_eq_mul],
  intros z hz,
  exact X_sub_C_ne_zero z
end

/- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
lemma deg_of_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).degree = nat.totient n :=
  by simp only [degree_eq_nat_degree (cycl'_ne_zero n R), nat_deg_of_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
lemma roots_of_cycl (n : ℕ) (R : Type*) [integral_domain R] :
  (cyclotomic' n R).roots = (primitive_roots n R).val :=
  by rw cyclotomic'; exact roots_prod_X_sub_C (primitive_roots n R)

end integral_domain

section field

variables {K : Type*} [field K]

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
lemma X_pow_sub_one_eq_prod {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
  X ^ n - C (1 : K) = ∏ ζ in nth_roots_finset n K, (X - C ζ) :=
begin
  rw [nth_roots_finset, ← multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h)],
  simp only [finset.prod_mk, ring_hom.map_one],
  rw [nth_roots],
  have hmonic : (X ^ n - C (1 : K)).monic := monic_X_pow_sub_C (1 : K) (ne_of_lt hpos).symm,
  symmetry,
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic,
  rw [@nat_degree_X_pow_sub_C K _ _ n hpos 1, ← nth_roots],
  exact is_primitive_root.card_nth_roots h
end

/-- `cyclotomic' n K` splits. -/
lemma cycl_splits (n : ℕ) : splits (ring_hom.id K) (cyclotomic' n K) :=
begin
  apply splits_prod (ring_hom.id K),
  intros z hz,
  simp only [splits_X_sub_C (ring_hom.id K)]
end

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
lemma X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) :
  splits (ring_hom.id K) (X ^ n - C (1 : K)) :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, ring_hom.map_one, splits_zero, pow_zero, sub_self] },
  apply (splits_iff_card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hzero) (1 : K))).2,
  rw [← nth_roots, is_primitive_root.card_nth_roots h, nat_degree_X_pow_sub_C],
  exact nat.pos_of_ne_zero hzero
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`X ^ n - 1 = ∏ (cyclotomic' i K)`, where `i` divides `n`. -/
lemma X_pow_sub_one_eq_prod_cycl' {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
  X ^ n - C (1 : K) = ∏ i in nat.divisors n, cyclotomic' i K :=
begin
  rw [X_pow_sub_one_eq_prod hpos h],
--  rw ← pnat.to_pnat'_coe hpos at h ⊢,
--  set m := nat.to_pnat' n,
  have rwcyc : ∀ i ∈ nat.divisors n, cyclotomic' i K = ∏ μ in primitive_roots i K, (X - C μ),
  { intros i hi,
    simp only [cyclotomic'] },
  conv_rhs { apply_congr,
             skip,
             simp [rwcyc, H] },
  rw ← finset.prod_bind,
  { simp only [is_primitive_root.nth_roots_one_eq_bind_primitive_roots hpos h] },
  intros x hx y hy hdiff,
  simp only [nat.mem_divisors, and_true, ne.def, pnat.ne_zero, not_false_iff] at hx hy,
  refine is_primitive_root.disjoint _ _ hdiff,
  exact @nat.pos_of_mem_divisors n x (nat.mem_divisors.2 hx),
  exact @nat.pos_of_mem_divisors n y (nat.mem_divisors.2 hy)
end

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
polynomial with integer coefficients. -/
lemma int_coeff_of_cycl {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) :
  (∃ (P : polynomial ℤ), map (int.cast_ring_hom K) P = cyclotomic' n K ∧
  P.degree = (cyclotomic' n K).degree ∧ P.monic) :=
begin
  refine lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K),
  revert h ζ,
  apply nat.strong_induction_on n,
  intros k hk z hzeta,
  by_cases hzero : k = 0,
  { use 1,
    simp only [hzero, cyclotomic'_zero, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
    map_one, ring_hom.coe_of, and_self], },
  have hpos := (nat.pos_of_ne_zero hzero),
  by_cases hone : k = 1,
  { use X - 1,
    simp only [hone, cyclotomic'_one K, set.mem_univ, pnat.one_coe, subsemiring.coe_top,
    eq_self_iff_true, map_X, map_one, ring_hom.coe_of, and_self, map_sub] },
  let B : polynomial K := ∏ i in nat.proper_divisors k, cyclotomic' i K,
  have Bmo : B.monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact (cyclotomic'.monic i K) },
  have Bint : B ∈ lifts (int.cast_ring_hom K),
  { refine subsemiring.prod_mem (lifts (int.cast_ring_hom K)) _,
    intros x hx,
    have xsmall := (nat.mem_proper_divisors.1 hx).2,
    obtain ⟨d, hd⟩ := (nat.mem_proper_divisors.1 hx).1,
    rw [mul_comm] at hd,
  refine hk x xsmall (is_primitive_root.pow (nat.pos_of_ne_zero hzero) hzeta hd) },
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo,
  obtain ⟨B₁, hB₁, hB₁deg, hB₁mo⟩ := Bint,
  let Q₁ : polynomial ℤ := (X ^ k - 1) /ₘ B₁,
  have huniq : 0 + B * (cyclotomic' k K) = (X ^ k - 1 :
  polynomial K) ∧ (0 : polynomial K).degree < B.degree,
  { split,
    { rw [zero_add, mul_comm, ← C_1, (X_pow_sub_one_eq_prod_cycl' hpos hzeta),
      nat.divisors_eq_proper_divisors_insert_self_of_pos hpos],
      simp only [true_and, finset.prod_insert, not_lt, nat.mem_proper_divisors, dvd_refl] },
    rw [degree_zero, bot_lt_iff_ne_bot],
    intro habs,
    exact (monic.ne_zero Bmo) (degree_eq_bot.1 habs) },
  replace huniq := div_mod_by_monic_unique (cyclotomic' k K) (0 : polynomial K) Bmo huniq,
  simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange],
  use Q₁,
  rw [(map_div_by_monic (int.cast_ring_hom K) hB₁mo), hB₁, ← huniq.1],
  simp only [map_pow, map_X, map_one, map_sub]
end

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
lemma unique_int_coeff_of_cycl [char_zero K] {ζ : K} {n : ℕ+} (h : is_primitive_root ζ n) :
  (∃! (P : polynomial ℤ), map (int.cast_ring_hom K) P = cyclotomic' n K) :=
begin
  obtain ⟨P, hP⟩ := int_coeff_of_cycl h,
  rw exists_unique,
  use P,
  split,
  exact hP.1,
  intros Q hQ,
  have mapinj : function.injective (map (int.cast_ring_hom K)),
  { apply map_injective,
    simp only [int.cast_injective, int.coe_cast_ring_hom] },
  rw [function.injective] at mapinj,
  apply mapinj,
  rw [hP.1, hQ]
end

end field

section integers

/-- The `n`-th cyclotomic polynomial with coefficients in `ℤ`. -/
def cyclotomic : ℕ → polynomial ℤ
| 0 := 1
| n@(k + 1) := classical.some (int_coeff_of_cycl
  (complex.is_primitive_root_exp n (nat.succ_ne_zero k)))

lemma cyclotomic_spec (n : ℕ) : map (int.cast_ring_hom ℂ) (cyclotomic n) =
cyclotomic' n ℂ ∧ (cyclotomic n).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n).monic  :=
begin
  by_cases hzero : n = 0,
  { simp only [cyclotomic, cyclotomic'_zero, hzero, degree_one, monic_one, eq_self_iff_true,
  map_one, and_self] },
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hzero,
  rw cyclotomic,
  exact classical.some_spec (int_coeff_of_cycl (complex.is_primitive_root_exp k.succ
  (nat.succ_ne_zero k)))
end

lemma cyclotomic_unique {n : ℕ} {P : polynomial ℤ} (h : map (int.cast_ring_hom ℂ) P =
  cyclotomic' n ℂ) : P = cyclotomic n :=
begin
  have mapinj : function.injective (map (int.cast_ring_hom ℂ)),
  { apply map_injective,
    simp only [int.cast_injective, int.coe_cast_ring_hom] },
  apply mapinj,
  rw [h, (cyclotomic_spec n).1]
end

/- The zeroth cyclotomic polyomial is `1`. -/
lemma cyclotomic_zero : cyclotomic 0 = 1 :=
by rw cyclotomic

/- The first cyclotomic polyomial is `X - 1`. -/
lemma cyclotomic_one : cyclotomic 1 = X - 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X - 1) = cyclotomic' 1 ℂ,
  { simp only [cyclotomic'_one, pnat.one_coe, map_X, map_one, map_sub] },
  symmetry,
  exact cyclotomic_unique hspec
end

/- The second cyclotomic polyomial is `X + 1`. -/
lemma cyclotomic_two : cyclotomic 2 = X + 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X + 1) = cyclotomic' 2 ℂ,
  { simp [cyclotomic'_two ℂ 0 two_ne_zero.symm] },
  symmetry,
  exact cyclotomic_unique hspec
end

/-- `cyclotomic n` is monic. -/
lemma cyclotomic.monic (n : ℕ) : (cyclotomic n).monic := (cyclotomic_spec n).2.2

/-- `cyclotomic n R` is different from `0`. -/
lemma cycl_ne_zero (n : ℕ) : cyclotomic n ≠ 0 := monic.ne_zero (cyclotomic.monic n)

/- The degree of `cyclotomic n` is `totient n`. -/
lemma deg_of_cyclotomic (n : ℕ) : (cyclotomic n).degree = nat.totient n :=
begin
  cases n with k, simp [cyclotomic],
  rw [←deg_of_cyclotomic' (complex.is_primitive_root_exp k.succ (nat.succ_ne_zero k))],
  exact (cyclotomic_spec k.succ).2.1
end

/- The natural degree of `cyclotomic n` is `totient n`. -/
lemma nat_deg_of_cyclotomic (n : ℕ) : (cyclotomic n).nat_degree = nat.totient n :=
begin
  have hdeg := deg_of_cyclotomic n,
  rw degree_eq_nat_degree (cycl_ne_zero n) at hdeg,
  norm_cast at hdeg,
  exact hdeg
end

/-- `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`. -/
lemma X_pow_sub_one_eq_prod_cycl (n : ℕ) (hpos : 0 < n) :
  X ^ n - 1 = ∏ i in nat.divisors ↑n, cyclotomic i :=
begin
  have mapinj : function.injective (ring_hom.of (map (int.cast_ring_hom ℂ))),
    { apply map_injective,
      simp only [int.cast_injective, int.coe_cast_ring_hom] },
  apply mapinj,
  rw ring_hom.map_prod (ring_hom.of (map (int.cast_ring_hom ℂ))) (λ i, cyclotomic i),
  simp only [cyclotomic_spec, map_pow, nat.cast_id, map_X, map_one, ring_hom.coe_of, map_sub],
  exact X_pow_sub_one_eq_prod_cycl' hpos (complex.is_primitive_root_exp n (ne_of_lt hpos).symm)
end

end integers

end polynomial
