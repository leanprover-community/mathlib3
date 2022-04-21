/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.ideal
import ring_theory.valuation.integers
import topology.algebra.valued_field

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

We define the completion of `K` with respect to the `v`-adic valuation, denoted
`v.adic_completion`,and its ring of integers, denoted `v.adic_completion_integers`.

## Main definitions
 - `is_dedekind_domain.height_one_spectrum.int_valuation v` is the `v`-adic valuation on `R`.
 - `is_dedekind_domain.height_one_spectrum.valuation v` is the `v`-adic valuation on `K`.
 - `is_dedekind_domain.height_one_spectrum.adic_completion v` is the completion of `K` with respect
    to its `v`-adic valuation.
 - `is_dedekind_domain.height_one_spectrum.adic_completion_integers v` is the ring of integers of
    `v.adic_completion`.

## Main results
- `is_dedekind_domain.height_one_spectrum.int_valuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `is_dedekind_domain.height_one_spectrum.int_valuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `is_dedekind_domain.height_one_spectrum.int_valuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than or equal to `multiplicative.of_add (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer` : There exists `π ∈ R`
  with `v`-adic valuation `multiplicative.of_add (-1)`.
- `is_dedekind_domain.height_one_spectrum.int_valuation_div_eq_div` : The valuation of `k ∈ K` is
  independent on how we express `k` as a fraction.
- `is_dedekind_domain.height_one_spectrum.valuation_of_mk'` : The `v`-adic valuation of `r/s ∈ K`
  is the valuation of `r` divided by the valuation of `s`.
- `is_dedekind_domain.height_one_spectrum.valuation_of_algebra_map` : The `v`-adic valuation on `K`
  extends the `v`-adic valuation on `R`.
- `is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer` : There exists `π ∈ K` with
  `v`-adic valuation `multiplicative.of_add (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable theory
open_locale classical

open multiplicative is_dedekind_domain

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

namespace is_dedekind_domain.height_one_spectrum
/-! ### Adic valuations on the Dedekind domain R -/

/-- The additive `v`-adic valuation of `r ∈ R` is the exponent of `v` in the factorization of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `int_valuation_def` is the corresponding
multiplicative valuation. -/
def int_valuation_def (r : R) : with_zero (multiplicative ℤ) :=
if r = 0 then 0 else multiplicative.of_add
  (-(associates.mk v.as_ideal).count (associates.mk (ideal.span {r} : ideal R)).factors : ℤ)

lemma int_valuation_def_if_pos {r : R} (hr : r = 0) : v.int_valuation_def r = 0 := if_pos hr

lemma int_valuation_def_if_neg {r : R} (hr : r ≠ 0) : v.int_valuation_def r = (multiplicative.of_add
  (-(associates.mk v.as_ideal).count (associates.mk (ideal.span {r} : ideal R)).factors : ℤ)) :=
if_neg hr

/-- Nonzero elements have nonzero adic valuation. -/
lemma int_valuation_ne_zero (x : R) (hx : x ≠ 0) : v.int_valuation_def x ≠ 0 :=
begin
  rw [int_valuation_def, if_neg hx],
  exact with_zero.coe_ne_zero,
end

/-- Nonzero divisors have nonzero valuation. -/
lemma int_valuation_ne_zero' (x : non_zero_divisors R) : v.int_valuation_def x ≠ 0 :=
v.int_valuation_ne_zero x (non_zero_divisors.coe_ne_zero x)

/-- Nonzero divisors have valuation greater than zero. -/
lemma int_valuation_zero_le (x : non_zero_divisors R) : 0 < v.int_valuation_def x :=
begin
  rw [v.int_valuation_def_if_neg (non_zero_divisors.coe_ne_zero x)],
  exact with_zero.zero_lt_coe _,
end

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
lemma int_valuation_le_one (x : R) : v.int_valuation_def x ≤ 1 :=
begin
  rw int_valuation_def,
  by_cases hx : x = 0,
  { rw if_pos hx, exact with_zero.zero_le 1 },
  { rw [if_neg hx, ← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, of_add_le,
      right.neg_nonpos_iff],
    exact int.coe_nat_nonneg _ }
end

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
lemma int_valuation_lt_one_iff_dvd (r : R) :
  v.int_valuation_def r < 1 ↔ v.as_ideal ∣ ideal.span {r} :=
begin
  rw int_valuation_def,
  split_ifs with hr,
  { simpa [hr] using (with_zero.zero_lt_coe _) },
  { rw [← with_zero.coe_one, ← of_add_zero, with_zero.coe_lt_coe, of_add_lt, neg_lt_zero,
      ← int.coe_nat_zero, int.coe_nat_lt, zero_lt_iff],
    have h : (ideal.span {r} : ideal R) ≠ 0,
    { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot],
      exact hr },
    apply associates.count_ne_zero_iff_dvd h (by apply v.irreducible) }
end

/-- The `v`-adic valuation of `r ∈ R` is less than `multiplicative.of_add (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
lemma int_valuation_le_pow_iff_dvd (r : R) (n : ℕ) :
  v.int_valuation_def r ≤ multiplicative.of_add (-(n : ℤ)) ↔ v.as_ideal^n ∣ ideal.span {r} :=
begin
  rw int_valuation_def,
  split_ifs with hr,
  { simp_rw [hr, ideal.dvd_span_singleton, zero_le', submodule.zero_mem], },
  { rw [with_zero.coe_le_coe, of_add_le, neg_le_neg_iff, int.coe_nat_le, ideal.dvd_span_singleton,
      ← associates.le_singleton_iff, associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hr)
      (by apply v.associates_irreducible)] }
end

/-- The `v`-adic valuation of `0 : R` equals 0. -/
lemma int_valuation.map_zero' : v.int_valuation_def 0 = 0 := v.int_valuation_def_if_pos (eq.refl 0)

/-- The `v`-adic valuation of `1 : R` equals 1. -/
lemma int_valuation.map_one' : v.int_valuation_def 1 = 1 :=
by rw [v.int_valuation_def_if_neg (zero_ne_one.symm : (1 : R) ≠ 0), ideal.span_singleton_one,
  ← ideal.one_eq_top, associates.mk_one, associates.factors_one, associates.count_zero
  (by apply v.associates_irreducible), int.coe_nat_zero, neg_zero, of_add_zero, with_zero.coe_one]

/-- The `v`-adic valuation of a product equals the product of the valuations. -/
lemma int_valuation.map_mul' (x y : R) :
  v.int_valuation_def (x * y) = v.int_valuation_def x * v.int_valuation_def y :=
begin
  simp only [int_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul, with_zero.coe_inj,
        ← of_add_add, ← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk, ← neg_add,
        associates.count_mul (by apply associates.mk_ne_zero'.mpr hx)
        (by apply associates.mk_ne_zero'.mpr hy) (by apply v.associates_irreducible)],
      refl }}
end

lemma int_valuation.le_max_iff_min_le {a b c : ℕ} :  multiplicative.of_add(-c : ℤ) ≤
  max (multiplicative.of_add(-a : ℤ)) (multiplicative.of_add(-b : ℤ)) ↔ min a b ≤ c :=
by rw [le_max_iff, of_add_le, of_add_le, neg_le_neg_iff, neg_le_neg_iff, int.coe_nat_le,
    int.coe_nat_le, ← min_le_iff]

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
lemma int_valuation.map_add_le_max' (x y : R) : v.int_valuation_def (x + y) ≤
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
        ((associates.mk v.as_ideal).count (associates.mk (ideal.span {x})).factors)
        ((associates.mk v.as_ideal).count (associates.mk (ideal.span {y})).factors),
      have h_dvd_x : x ∈ v.as_ideal ^ (nmin),
      { rw [← associates.le_singleton_iff x nmin _,
          associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hx) _],
        exact min_le_left _ _,
        apply v.associates_irreducible },
      have h_dvd_y : y ∈ v.as_ideal ^ nmin,
      { rw [← associates.le_singleton_iff y nmin _,
          associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hy) _],
        exact min_le_right _ _,
        apply v.associates_irreducible },
      have h_dvd_xy : associates.mk v.as_ideal^nmin ≤ associates.mk (ideal.span {x + y}),
      { rw associates.le_singleton_iff,
        exact ideal.add_mem (v.as_ideal^nmin) h_dvd_x h_dvd_y, },
      rw (associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hxy) _) at h_dvd_xy,
      exact h_dvd_xy,
      apply v.associates_irreducible, }}}
end

/-- The `v`-adic valuation on `R`. -/
def int_valuation : valuation R (with_zero (multiplicative ℤ)) :=
{ to_fun          := v.int_valuation_def,
  map_zero'       := int_valuation.map_zero' v,
  map_one'        := int_valuation.map_one' v,
  map_mul'        := int_valuation.map_mul' v,
  map_add_le_max' := int_valuation.map_add_le_max' v }

/-- There exists `π ∈ R` with `v`-adic valuation `multiplicative.of_add (-1)`. -/
lemma int_valuation_exists_uniformizer :
  ∃ (π : R), v.int_valuation_def π = multiplicative.of_add (-1 : ℤ) :=
begin
  have hv : _root_.irreducible (associates.mk v.as_ideal) := v.associates_irreducible,
  have hlt : v.as_ideal^2 < v.as_ideal,
  { rw ← ideal.dvd_not_unit_iff_lt,
    exact ⟨v.ne_bot, v.as_ideal,
     (not_congr ideal.is_unit_iff).mpr (ideal.is_prime.ne_top v.is_prime), sq v.as_ideal⟩ } ,
  obtain ⟨π, mem, nmem⟩ := set_like.exists_of_lt hlt,
  have hπ : associates.mk (ideal.span {π}) ≠ 0,
  { rw associates.mk_ne_zero',
    intro h,
    rw h at nmem,
    exact nmem (submodule.zero_mem (v.as_ideal^2)), },
  use π,
  rw [int_valuation_def, if_neg (associates.mk_ne_zero'.mp hπ), with_zero.coe_inj],
  apply congr_arg,
  rw [neg_inj, ← int.coe_nat_one, int.coe_nat_inj'],
  rw [← ideal.dvd_span_singleton, ← associates.mk_le_mk_iff_dvd_iff] at mem nmem,
  rw [← pow_one ( associates.mk v.as_ideal),
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
lemma int_valuation_div_eq {r r' : R} {s s' : non_zero_divisors R}
  (h_mk : is_localization.mk' K r s = is_localization.mk' K r' s') :
  (v.int_valuation_def r)/(v.int_valuation_def s) =
  (v.int_valuation_def r')/(v.int_valuation_def s') :=
begin
  rw [div_eq_div_iff (int_valuation_ne_zero' v s) (int_valuation_ne_zero' v s'),
    ← int_valuation.map_mul', ← int_valuation.map_mul',
    is_fraction_ring.injective R K (is_localization.mk'_eq_iff_eq.mp h_mk)],
end

/-- The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by the valuation of `s`. -/
lemma valuation_of_mk' {r : R} {s : non_zero_divisors R} :
  v.valuation_def (is_localization.mk' K r s) = (v.int_valuation_def r)/(v.int_valuation_def s) :=
begin
  rw valuation_def,
  exact int_valuation_div_eq K v
    (classical.some_spec (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R)
    (is_localization.mk' K r s)))),
end

variable {K}
/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
lemma valuation_of_algebra_map (r : R) :
  v.valuation_def (algebra_map R K r) = v.int_valuation_def r :=
by rw [← is_localization.mk'_one K r, valuation_of_mk', submonoid.coe_one,
    int_valuation.map_one', div_one _]

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
lemma valuation_le_one (r : R) : v.valuation_def (algebra_map R K r) ≤ 1 :=
by { rw valuation_of_algebra_map, exact v.int_valuation_le_one r }

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
lemma valuation_lt_one_iff_dvd (r : R) :
  v.valuation_def (algebra_map R K r) < 1 ↔ v.as_ideal ∣ ideal.span {r} :=
by { rw valuation_of_algebra_map, exact v.int_valuation_lt_one_iff_dvd r }

/-- The `v`-adic valuation of `0 : K` equals 0. -/
lemma valuation.map_zero' : v.valuation_def (0 : K) = 0 :=
begin
  rw [← (algebra_map R K).map_zero, valuation_of_algebra_map v],
  exact v.int_valuation.map_zero',
end

/-- The `v`-adic valuation of `1 : K` equals 1. -/
lemma valuation.map_one' : v.valuation_def (1 : K) = 1 :=
begin
  rw [← (algebra_map R K).map_one, valuation_of_algebra_map v],
  exact v.int_valuation.map_one',
end

/-- The `v`-adic valuation of a product is the product of the valuations. -/
lemma valuation.map_mul' (x y : K) :
  v.valuation_def (x * y) = v.valuation_def x * v.valuation_def y :=
begin
  rw [valuation_def, valuation_def, valuation_def, div_mul_div_comm₀, ← int_valuation.map_mul',
    ← int_valuation.map_mul', ← submonoid.coe_mul],
  apply int_valuation_div_eq K v,
  rw [(classical.some_spec (valuation_def._proof_2 (x * y))), is_fraction_ring.mk'_eq_div,
    (algebra_map R K).map_mul, submonoid.coe_mul, (algebra_map R K).map_mul, ← div_mul_div_comm₀,
    ← is_fraction_ring.mk'_eq_div, ← is_fraction_ring.mk'_eq_div,
    (classical.some_spec (valuation_def._proof_2 x)),
    (classical.some_spec (valuation_def._proof_2 y))],
end

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
lemma valuation.map_add_le_max' (x y : K) :
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
  rw [int_valuation_div_eq K v h_frac_x, int_valuation_div_eq K v h_frac_y,
    int_valuation_div_eq K v h_frac_xy, le_max_iff, div_le_div_right₀ (ne_of_gt h_denom),
    div_le_div_right₀ (ne_of_gt h_denom), ← le_max_iff],
  exact v.int_valuation.map_add_le_max' _ _,
end

/-- The `v`-adic valuation on `K`. -/
def valuation  : valuation K (with_zero (multiplicative ℤ)) :=
{ to_fun    := v.valuation_def,
  map_zero' := valuation.map_zero' v,
  map_one'  := valuation.map_one' v,
  map_mul'  := valuation.map_mul' v,
  map_add_le_max'  := valuation.map_add_le_max' v }

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

/-! ### Completions with respect to adic valuations
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adic_completion`, and its
ring of integers, denoted `v.adic_completion_integers`. -/

variable {K}

/-- `K` as a valued field with the `v`-adic valuation. -/
def adic_valued : valued K (with_zero (multiplicative ℤ)) := ⟨v.valuation⟩

lemma adic_valued_def {x : K} : (v.adic_valued.v : _) x = v.valuation_def x := rfl

/-- The topological space structure on `K` corresponding to the `v`-adic valuation.
  This cannot be made an instance since it depends on the choice of `v`. -/
def adic_valued_topological_space : topological_space K :=
@valued.topological_space K _ _ _ v.adic_valued

lemma adic_valued_topological_division_ring :
  @topological_division_ring K _ v.adic_valued_topological_space :=
infer_instance

lemma adic_valued_topological_ring : @topological_ring K  v.adic_valued_topological_space _ :=
infer_instance

lemma adic_valued_topological_add_group :
  @topological_add_group K v.adic_valued_topological_space _ := infer_instance

/-- The uniform space structure on `K` corresponding to the `v`-adic valuation. -/
def adic_valued_uniform_space : uniform_space K :=
@topological_add_group.to_uniform_space K _ v.adic_valued_topological_space
  v.adic_valued_topological_add_group

lemma adic_valued_uniform_add_group : @uniform_add_group K v.adic_valued_uniform_space _ :=
@topological_add_group_is_uniform K _ v.adic_valued_topological_space
  v.adic_valued_topological_add_group

lemma adic_valued_completable_top_field : @completable_top_field K _ v.adic_valued_uniform_space :=
@valued.completable K _ _ _ (adic_valued v)

lemma adic_valued_separated_space : @separated_space K v.adic_valued_uniform_space :=
@valued_ring.separated K _ _ _ (adic_valued v)

variables (K)

/-- The completion of `K` with respect to its `v`-adic valuation. -/
def adic_completion := @uniform_space.completion K v.adic_valued_uniform_space

instance : field (v.adic_completion K) :=
@field_completion K _ v.adic_valued_uniform_space v.adic_valued_topological_division_ring _
  v.adic_valued_uniform_add_group

instance : inhabited (v.adic_completion K) := ⟨0⟩

variables {K}
instance valued_adic_completion : valued (v.adic_completion K) (with_zero (multiplicative ℤ)) :=
⟨@valued.extension_valuation K _ _ _ v.adic_valued⟩

lemma valued_adic_completion_def {x : v.adic_completion K} :
  valued.v (x) = @valued.extension K _ _ _ (adic_valued v)  x := rfl

instance adic_completion_topological_division_ring :
  topological_division_ring (v.adic_completion K) :=
@valued.topological_division_ring (v.adic_completion K) _ _ _ v.valued_adic_completion

instance adic_completion_topological_space : topological_space (v.adic_completion K) :=
infer_instance

instance adic_completion_uniform_space : uniform_space (v.adic_completion K) :=
@uniform_space.completion.uniform_space K v.adic_valued_uniform_space

instance adic_completion_uniform_add_group :
  @uniform_add_group (v.adic_completion K) v.adic_completion_uniform_space _ :=
@uniform_space.completion.uniform_add_group K v.adic_valued_uniform_space _
  v.adic_valued_uniform_add_group

instance adic_completion_complete_space : complete_space (v.adic_completion K) :=
@uniform_space.completion.complete_space K v.adic_valued_uniform_space

instance : has_lift_t K (@uniform_space.completion K v.adic_valued_uniform_space) := infer_instance

instance adic_completion.has_lift_t : has_lift_t K (v.adic_completion K) :=
uniform_space.completion.has_lift_t v

variables (K)
/-- The ring of integers of `adic_completion`. -/
def adic_completion_integers : subring (v.adic_completion K) :=
@valuation.integer (v.adic_completion K) (with_zero (multiplicative ℤ)) _ _
  v.valued_adic_completion.v

end is_dedekind_domain.height_one_spectrum
