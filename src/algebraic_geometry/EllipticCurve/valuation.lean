/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import algebraic_geometry.prime_spectrum.basic
import ring_theory.dedekind_domain.ideal
import topology.algebra.valued_field

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

## Main definitions
 - `maximal_spectrum` defines the set of nonzero prime ideals of `R`. When `R` is a Dedekind domain
   of Krull dimension 1, this is the set of maximal ideals of `R`.
 - `maximal_spectrum.int_valuation v` is the `v`-adic valuation on `R`.
 - `maximal_spectrum.valuation v` is the `v`-adic valuation on `K`.

## Main results
- `int_valuation_le_one` : The `v`-adic valuation on `R` is bounded above by 1.
- `int_valuation_lt_one_iff_dvd` : The `v`-adic valuation of `r ∈ R` is less than 1 if and only if
  `v` divides the ideal `(r)`.
- `int_valuation_le_pow_iff_dvd` : The `v`-adic valuation of `r ∈ R` is less than or equal to
  `multiplicative.of_add (-n)` if and only if `vⁿ` divides the ideal `(r)`.
- `int_valuation_exists_uniformizer` : There exists `π ∈ R` with `v`-adic valuation
  `multiplicative.of_add (-1)`.
- `valuation_well_defined` : The valuation of `k ∈ K` is independent on how we express `k`
  as a fraction.
- `valuation_of_mk'` : The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by
  the valuation of `s`.
- `valuation_of_algebra_map` : The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`.
- `valuation_exists_uniformizer` : There exists `π ∈ K` with `v`-adic valuation
  `multiplicative.of_add (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1. Dedekind domains of Krull
dimension 0 are fields, and for them `maximal_spectrum` is the empty set, which does not agree with
the set of maximal ideals (which is {(0)}).

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable theory
open_locale classical

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K]

/-!
### Maximal spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.

We define `maximal_spectrum` and provide lemmas to recover the facts that maximal ideals are prime
and irreducible. -/

/-- The maximal spectrum of a Dedekind domain `R` of Krull dimension 1 is its set of nonzero prime
ideals. Note that this is not the maximal spectrum if `R` has Krull dimension 0. -/
def maximal_spectrum := {v : prime_spectrum R // v.val ≠ 0 }
variable (v : maximal_spectrum R)

variable {R}
--Maximal spectrum lemmas
lemma ideal.prime_of_maximal (v : maximal_spectrum R) :
  prime v.val.val :=
by apply ideal.prime_of_is_prime v.property v.val.property

lemma ideal.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible v.val.val :=
begin
  rw [unique_factorization_monoid.irreducible_iff_prime],
  apply ideal.prime_of_maximal v,
end

lemma associates.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible (associates.mk v.val.val) :=
begin
  rw [associates.irreducible_mk _],
  apply ideal.irreducible_of_maximal v,
end

/-!
### Auxiliary lemmas
We provide auxiliary lemmas about `multiplicative.of_add`, `is_localization`, `associates` and
`ideal`. They will be moved to the appropriate files when the code is integrated in `mathlib`. -/

-- of_add lemmas
lemma of_add_le (α : Type*) [partial_order α] (x y : α) :
  multiplicative.of_add x ≤ multiplicative.of_add y ↔ x ≤ y := by refl

lemma of_add_lt (α : Type*) [partial_order α] (x y : α) :
  multiplicative.of_add x < multiplicative.of_add y ↔ x < y := by refl

lemma of_add_inj (α : Type*) (x y : α)
  (hxy : multiplicative.of_add x = multiplicative.of_add y) : x = y :=
by rw [← to_add_of_add x, ← to_add_of_add y, hxy]

variables {A : Type*} [comm_ring A] [is_domain A] {S : Type*} [field S] [algebra A S]
  [is_fraction_ring A S]

lemma is_localization.mk'_eq_zero {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 0) : r = 0 :=
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_zero_iff] at h,
  apply is_fraction_ring.injective A S,
  rw (algebra_map A S).map_zero,
  exact or.resolve_right h (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property)
end

variable (S)
lemma is_localization.mk'_eq_one {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 1) : r = s :=
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_one_iff_eq] at h,
  { exact is_fraction_ring.injective A S h },
  { exact is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property }
end

-- Ideal associates lemmas
lemma associates.mk_ne_zero' {α : Type*} [comm_ring α] {x : α} :
  (associates.mk (ideal.span{x} : ideal α)) ≠ 0 ↔ (x ≠ 0):=
by rw [associates.mk_ne_zero, ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot]

lemma associates.le_singleton_iff (x : R) (n : ℕ) (I : ideal R) :
  associates.mk I^n ≤ associates.mk (ideal.span {x}) ↔ x ∈ I^n :=
begin
  rw [← associates.dvd_eq_le, ← associates.mk_pow, associates.mk_dvd_mk, ideal.dvd_span_singleton],
end

-- Ideal lemmas
lemma ideal.mem_pow_count {x : R} (hx : x ≠ 0) {I : ideal R} (hI : irreducible I) :
  x ∈ I^((associates.mk I).count (associates.mk (ideal.span {x})).factors) :=
begin
  have hx' := associates.mk_ne_zero'.mpr hx,
  rw [← associates.le_singleton_iff,
    associates.prime_pow_dvd_iff_le hx' ((associates.irreducible_mk I).mpr hI)],
end

lemma ideal.mem_le_pow {x : R} {I : ideal R} {n : ℕ} (hxI : x ∈ I^n) (m : ℕ) (hm : m ≤ n) :
  x ∈ I^m := ideal.pow_le_pow hm hxI

lemma ideal.is_nonunit_iff {I : ideal R} : ¬ is_unit I ↔ I ≠ ⊤ := not_congr ideal.is_unit_iff

namespace maximal_spectrum
/-! ### Adic valuations on the Dedekind domain R -/

/-- The additive `v`-adic valuation of `r ∈ R` is the exponent of `v` in the factorization of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `int_valuation_def` is the corresponding
multiplicative valuation. -/
def int_valuation_def (r : R) : with_zero (multiplicative ℤ) :=
ite (r = 0) 0 (multiplicative.of_add
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ))

lemma int_valuation_def_if_pos {r : R} (hr : r = 0) :
  v.int_valuation_def r = 0 :=
if_pos hr

lemma int_valuation_def_if_neg {r : R} (hr : r ≠ 0) :
  v.int_valuation_def r = (multiplicative.of_add
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ)) :=
if_neg hr

/-- Nonzero elements have nonzero adic valuation. -/
lemma int_valuation_ne_zero' (x : R) (hx : x ≠ 0) : v.int_valuation_def x ≠ 0 :=
begin
  rw [int_valuation_def, if_neg hx],
  exact with_zero.coe_ne_zero,
end

/-- Nonzero divisors have nonzero valuation. -/
lemma int_valuation_ne_zero (x : non_zero_divisors R) : v.int_valuation_def x ≠ 0 :=
int_valuation_ne_zero' v x (non_zero_divisors.coe_ne_zero x)

/-- Nonzero divisors have valuation greater than zero. -/
lemma int_valuation_zero_le (x : non_zero_divisors R) : 0 < v.int_valuation_def x :=
begin
  rw [int_valuation_def, if_neg (non_zero_divisors.coe_ne_zero x)],
  exact with_zero.zero_lt_coe _,
end

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
lemma int_valuation_le_one (x : R) : v.int_valuation_def x ≤ 1 :=
begin
  rw int_valuation_def,
  by_cases hx : x = 0,
  { rw if_pos hx, exact with_zero.zero_le 1,},
  { rw [if_neg hx, ← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, of_add_le,
      right.neg_nonpos_iff],
    exact int.coe_nat_nonneg _, }
end

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
lemma int_valuation_lt_one_iff_dvd (r : R) :
  v.int_valuation_def r < 1 ↔ v.val.val ∣ ideal.span {r} :=
begin
  rw int_valuation_def,
  split_ifs with hr,
  { simpa [hr] using (with_zero.zero_lt_coe _) },
  { rw [← with_zero.coe_one, ← of_add_zero, with_zero.coe_lt_coe, of_add_lt, neg_lt_zero,
      ← int.coe_nat_zero, int.coe_nat_lt, zero_lt_iff],
    apply associates.count_ne_zero_iff_dvd,
    { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact hr },
    { apply ideal.irreducible_of_maximal v }}
end

/-- The `v`-adic valuation of `r ∈ R` is less than `multiplicative.of_add (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
lemma int_valuation_le_pow_iff_dvd (r : R) (n : ℕ) :
  v.int_valuation_def r ≤ multiplicative.of_add (-(n : ℤ)) ↔ v.val.val^n ∣ ideal.span {r} :=
begin
  rw int_valuation_def,
  split_ifs with hr,
  { simp only [hr, ideal.dvd_span_singleton, zero_le', submodule.zero_mem], },
  { norm_cast,
    rw [of_add_le, neg_le_neg_iff, int.coe_nat_le, ideal.dvd_span_singleton,
    ← associates.le_singleton_iff,
    associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hr) _],
    { apply (associates.irreducible_of_maximal v) }}
end

/-- The `v`-adic valuation of `0 : R` equals 0. -/
lemma int_valuation.map_zero' : v.int_valuation_def 0 = 0 :=
by { rw [int_valuation_def, if_pos], refl, }

/-- The `v`-adic valuation of `1 : R` equals 1. -/
lemma int_valuation.map_one' : v.int_valuation_def 1 = 1 :=
begin
  rw [int_valuation_def, if_neg (zero_ne_one.symm : (1 : R) ≠ 0)],
  simp [← ideal.one_eq_top, -subtype.val_eq_coe,
    associates.count_zero (associates.irreducible_of_maximal v)],
end

/-- The `v`-adic valuation of a product equals the product of the valuations. -/
lemma int_valuation.map_mul' (x y : R) :
  v.int_valuation_def (x * y) = v.int_valuation_def x * v.int_valuation_def y :=
begin
  rw [int_valuation_def, int_valuation_def, int_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add],
      have hx' : associates.mk (ideal.span{x} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hx,
      have hy' : associates.mk (ideal.span{y} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hy,
      rw [← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk, ← neg_add,
        associates.count_mul hx' hy' _],
      { refl },
      { apply (associates.irreducible_of_maximal v), }}}
end

lemma int_valuation.le_max_iff_min_le {a b c : ℕ} :  multiplicative.of_add(-c : ℤ) ≤
  max (multiplicative.of_add(-a : ℤ)) (multiplicative.of_add(-b : ℤ)) ↔ min a b ≤ c :=
by rw [le_max_iff, of_add_le, of_add_le, neg_le_neg_iff, neg_le_neg_iff, int.coe_nat_le,
    int.coe_nat_le, ← min_le_iff]

@[simp] lemma with_zero.le_max_iff {M : Type} [linear_ordered_comm_monoid M] {a b c : M} :
  (a : with_zero M) ≤ max b c ↔ a ≤ max b c :=
by simp only [with_zero.coe_le_coe, le_max_iff]

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
lemma int_valuation.map_add' (x y : R) : v.int_valuation_def (x + y) ≤
  max (v.int_valuation_def x) (v.int_valuation_def y) :=
begin
  by_cases hx : x = 0,
  { rw [hx, zero_add],
    conv_rhs {rw [int_valuation_def, if_pos (eq.refl _)]},
    rw max_eq_right (with_zero.zero_le (v.int_valuation_def y)),
    exact le_refl _, },
  { by_cases hy : y = 0,
    { rw [hy, add_zero],
      conv_rhs {rw [max_comm, int_valuation_def, if_pos (eq.refl _)]},
      rw max_eq_right (with_zero.zero_le (v.int_valuation_def x)),
      exact le_refl _ },
    { by_cases hxy : x + y = 0,
      { rw [int_valuation_def, if_pos hxy], exact zero_le',},
      { rw [v.int_valuation_def_if_neg hxy, v.int_valuation_def_if_neg hx,
          v.int_valuation_def_if_neg hy, with_zero.le_max_iff, int_valuation.le_max_iff_min_le],
      set nmin := min
        ((associates.mk v.val.val).count (associates.mk (ideal.span {x})).factors)
        ((associates.mk v.val.val).count (associates.mk (ideal.span {y})).factors),
      have h_dvd_x : x ∈ v.val.val ^ (nmin),
      { rw [← associates.le_singleton_iff x nmin _,
          associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hx) _],
        exact min_le_left _ _,
        apply associates.irreducible_of_maximal v, },
      have h_dvd_y : y ∈ v.val.val ^ nmin,
      { rw [← associates.le_singleton_iff y nmin _,
          associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hy) _],
        exact min_le_right _ _,
        apply associates.irreducible_of_maximal v, },
      have h_dvd_xy : associates.mk v.val.val^nmin ≤ associates.mk (ideal.span {x + y}),
      { rw associates.le_singleton_iff,
        exact ideal.add_mem (v.val.val^nmin) h_dvd_x h_dvd_y, },
      rw (associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hxy) _) at h_dvd_xy,
      exact h_dvd_xy,
      apply associates.irreducible_of_maximal v, }}}
end

/-- The `v`-adic valuation on `R`. -/
def int_valuation (v : maximal_spectrum R) : valuation R (with_zero (multiplicative ℤ)) :=
{ to_fun          := v.int_valuation_def,
  map_zero'       := int_valuation.map_zero' v,
  map_one'        := int_valuation.map_one' v,
  map_mul'        := int_valuation.map_mul' v,
  map_add_le_max' := int_valuation.map_add' v }

/-- There exists `π ∈ R` with `v`-adic valuation `multiplicative.of_add (-1)`. -/
lemma int_valuation_exists_uniformizer :
  ∃ (π : R), v.int_valuation_def π = multiplicative.of_add (-1 : ℤ) :=
begin
  have hv : irreducible (associates.mk v.val.val) := associates.irreducible_of_maximal v,
  have hlt : v.val.val^2 < v.val.val,
  { rw ← ideal.dvd_not_unit_iff_lt,
    exact ⟨v.property, v.val.val,
     ideal.is_nonunit_iff.mpr (ideal.is_prime.ne_top v.val.property), sq v.val.val⟩ } ,
  obtain ⟨π, mem, nmem⟩ := set_like.exists_of_lt hlt,
  have hπ : associates.mk (ideal.span {π}) ≠ 0,
  { rw associates.mk_ne_zero',
    intro h,
    rw h at nmem,
    exact nmem (submodule.zero_mem (v.val.val^2)), },
  use π,
  rw [int_valuation_def, if_neg (associates.mk_ne_zero'.mp hπ), with_zero.coe_inj],
  apply congr_arg,
  rw [neg_inj, ← int.coe_nat_one, int.coe_nat_inj'],
  rw [← ideal.dvd_span_singleton, ← associates.mk_le_mk_iff_dvd_iff] at mem nmem,
  rw [← pow_one ( associates.mk v.val.val),
    associates.prime_pow_dvd_iff_le hπ hv]  at mem,
  rw [associates.mk_pow, associates.prime_pow_dvd_iff_le hπ hv, not_le] at nmem,
  exact nat.eq_of_le_of_lt_succ mem nmem,
end

/-! ### Adic valuations on the field of fractions `K` -/
/-- The `v`-adic valuation of `x ∈ K` is the valuation of `r` divided by the valuation of `s`,
where `r` and `s` are chosen so that `x = r/s`. -/
def valuation_def (x : K) : (with_zero (multiplicative ℤ)) :=
let s := classical.some (classical.some_spec (is_localization.mk'_surjective
  (non_zero_divisors R) x)) in (v.int_valuation_def (classical.some
    (is_localization.mk'_surjective (non_zero_divisors R) x)))/(v.int_valuation_def s)

variable (K)
/-- The valuation of `k ∈ K` is independent on how we express `k` as a fraction. -/
lemma valuation_well_defined {r r' : R} {s s' : non_zero_divisors R}
  (h_mk : is_localization.mk' K r s = is_localization.mk' K r' s') :
  (v.int_valuation_def r)/(v.int_valuation_def s) =
  (v.int_valuation_def r')/(v.int_valuation_def s') :=
begin
  rw [div_eq_div_iff (int_valuation_ne_zero v s) (int_valuation_ne_zero v s'),
  ← int_valuation.map_mul', ← int_valuation.map_mul',
  is_fraction_ring.injective R K (is_localization.mk'_eq_iff_eq.mp h_mk)],
end

/-- The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by the valuation of `s`. -/
lemma valuation_of_mk' {r : R} {s : non_zero_divisors R} :
  v.valuation_def (is_localization.mk' K r s) =
   (v.int_valuation_def r)/(v.int_valuation_def s) :=
begin
  rw valuation_def,
  exact valuation_well_defined K v
    (classical.some_spec (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R)
    (is_localization.mk' K r s)))),
end

variable {K}
/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
lemma valuation_of_algebra_map {r : R} :
  v.valuation_def (algebra_map R K r) = v.int_valuation_def r :=
by rw [← is_localization.mk'_one K r, valuation_of_mk', submonoid.coe_one,
    int_valuation.map_one', div_one _]

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
lemma valuation_le_one (r : R) : v.valuation_def (algebra_map R K r) ≤ 1 :=
by { rw valuation_of_algebra_map, exact v.int_valuation_le_one r }

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
lemma valuation_lt_one_iff_dvd (r : R) :
  v.valuation_def (algebra_map R K r) < 1 ↔ v.val.val ∣ ideal.span {r} :=
by { rw valuation_of_algebra_map, exact v.int_valuation_lt_one_iff_dvd r }

/-- The `v`-adic valuation of `0 : R` equals 0. -/
lemma valuation.map_zero' (v : maximal_spectrum R) :
  v.valuation_def (0 : K) = 0 :=
begin
  rw [← (algebra_map R K).map_zero, valuation_of_algebra_map v],
  exact v.int_valuation.map_zero',
end

/-- The `v`-adic valuation of `1 : R` equals 1. -/
lemma valuation.map_one' (v : maximal_spectrum R) :
  v.valuation_def (1 : K) = 1 :=
begin
  rw [← (algebra_map R K).map_one, valuation_of_algebra_map v],
  exact v.int_valuation.map_one',
end

/-- The `v`-adic valuation of a product is the product of the valuations. -/
lemma valuation.map_mul' (v : maximal_spectrum R) (x y : K) :
  v.valuation_def (x * y) = v.valuation_def x * v.valuation_def y :=
begin
  rw [valuation_def, valuation_def, valuation_def, div_mul_div_comm₀,
    ← int_valuation.map_mul', ← int_valuation.map_mul', ← submonoid.coe_mul],
  apply valuation_well_defined K v,
  rw [(classical.some_spec (valuation_def._proof_2 (x * y))), is_fraction_ring.mk'_eq_div,
    (algebra_map R K).map_mul, submonoid.coe_mul, (algebra_map R K).map_mul, ← div_mul_div_comm₀,
    ← is_fraction_ring.mk'_eq_div, ← is_fraction_ring.mk'_eq_div,
    (classical.some_spec (valuation_def._proof_2 x)),
    (classical.some_spec (valuation_def._proof_2 y))],
end

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
lemma valuation.map_add' (v : maximal_spectrum R) (x y : K) :
  v.valuation_def (x + y) ≤ max (v.valuation_def x) (v.valuation_def y) :=
begin
  obtain ⟨rx, sx, hx⟩ := is_localization.mk'_surjective (non_zero_divisors R) x,
  obtain ⟨rxy, sxy, hxy⟩ := is_localization.mk'_surjective (non_zero_divisors R) (x + y),
  obtain ⟨ry, sy, hy⟩ := is_localization.mk'_surjective (non_zero_divisors R) y,
  rw [← hxy, ← hx, ← hy, valuation_of_mk', valuation_of_mk', valuation_of_mk'],
  have h_frac_xy : is_localization.mk' K rxy sxy =
    is_localization.mk' K (rx*(sy : R) + ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_add, hx, hy, hxy], },
  have h_frac_x : is_localization.mk' K rx sx = is_localization.mk' K (rx*(sy : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc, mul_comm (sy : R) _], },
  have h_frac_y : is_localization.mk' K ry sy = is_localization.mk' K (ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc], },
  have h_denom : 0 < v.int_valuation_def ↑(sx * sy),
  { rw [int_valuation_def, if_neg _],
    { exact with_zero.zero_lt_coe _ },
    { exact non_zero_divisors.ne_zero
        (submonoid.mul_mem (non_zero_divisors R) sx.property sy.property), }},
  rw [valuation_well_defined K v h_frac_x, valuation_well_defined K v h_frac_y,
    valuation_well_defined K v h_frac_xy, le_max_iff, div_le_div_right₀ (ne_of_gt h_denom),
    div_le_div_right₀ (ne_of_gt h_denom), ← le_max_iff],
  exact v.int_valuation.map_add_le_max' _ _,
end

/-- The `v`-adic valuation on `K`. -/
def valuation (v : maximal_spectrum R) : valuation K (with_zero (multiplicative ℤ)) :=
{ to_fun          := v.valuation_def,
  map_zero'       := valuation.map_zero' v,
  map_one'        := valuation.map_one' v,
  map_mul'        := valuation.map_mul' v,
  map_add_le_max' := valuation.map_add' v }

variable (K)
/-- There exists `π ∈ K` with `v`-adic valuation `multiplicative.of_add (-1)`. -/
lemma valuation_exists_uniformizer :
  ∃ (π : K), v.valuation_def π = multiplicative.of_add (-1 : ℤ) :=
begin
  obtain ⟨r, hr⟩ := v.int_valuation_exists_uniformizer,
  use algebra_map R K r,
  rw valuation_of_algebra_map v,
  exact hr,
end

/-- Uniformizers are nonzero. -/
lemma valuation_uniformizer_ne_zero :
  (classical.some (v.valuation_exists_uniformizer K)) ≠ 0 :=
begin
  have hu := (classical.some_spec (v.valuation_exists_uniformizer K)),
  have h : v.valuation_def (classical.some _) = valuation v (classical.some _) := rfl,
  rw h at hu,
  exact (valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu with_zero.coe_ne_zero),
end

end maximal_spectrum
