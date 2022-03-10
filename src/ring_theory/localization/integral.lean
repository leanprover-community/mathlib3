/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import data.equiv.ring
import group_theory.monoid_localization
import ring_theory.algebraic
import ring_theory.ideal.local_ring
import ring_theory.ideal.quotient
import ring_theory.integral_closure
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer
import ring_theory.non_zero_divisors
import group_theory.submonoid.inverses
import tactic.ring_exp

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) {S : Type*} [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open_locale big_operators polynomial

namespace is_localization

section integer_normalization

open polynomial

variables (M) {S} [is_localization M S]

open_locale classical

/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeff_integer_normalization (p : S[X]) (i : ℕ) : R :=
if hi : i ∈ p.support
then classical.some (classical.some_spec
      (exist_integer_multiples_of_finset M (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩))
else 0

lemma coeff_integer_normalization_of_not_mem_support (p : S[X]) (i : ℕ)
  (h : coeff p i = 0) : coeff_integer_normalization M p i = 0 :=
by simp only [coeff_integer_normalization, h, mem_support_iff, eq_self_iff_true, not_true,
  ne.def, dif_neg, not_false_iff]

lemma coeff_integer_normalization_mem_support (p : S[X]) (i : ℕ)
  (h : coeff_integer_normalization M p i ≠ 0) : i ∈ p.support :=
begin
  contrapose h,
  rw [ne.def, not_not, coeff_integer_normalization, dif_neg h]
end

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integer_normalization (p : S[X]) :
  R[X] :=
∑ i in p.support, monomial i (coeff_integer_normalization M p i)

@[simp]
lemma integer_normalization_coeff (p : S[X]) (i : ℕ) :
  (integer_normalization M p).coeff i = coeff_integer_normalization M p i :=
by simp [integer_normalization, coeff_monomial, coeff_integer_normalization_of_not_mem_support]
  {contextual := tt}

lemma integer_normalization_spec (p : S[X]) :
  ∃ (b : M), ∀ i,
    algebra_map R S ((integer_normalization M p).coeff i) = (b : R) • p.coeff i :=
begin
  use classical.some (exist_integer_multiples_of_finset M (p.support.image p.coeff)),
  intro i,
  rw [integer_normalization_coeff, coeff_integer_normalization],
  split_ifs with hi,
  { exact classical.some_spec (classical.some_spec
      (exist_integer_multiples_of_finset M (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩)) },
  { convert (smul_zero _).symm,
    { apply ring_hom.map_zero },
    { exact not_mem_support_iff.mp hi } }
end

lemma integer_normalization_map_to_map (p : S[X]) :
  ∃ (b : M), (integer_normalization M p).map (algebra_map R S) = (b : R) • p :=
let ⟨b, hb⟩ := integer_normalization_spec M p in
⟨b, polynomial.ext (λ i, by { rw [coeff_map, coeff_smul], exact hb i })⟩

variables {R' : Type*} [comm_ring R']

lemma integer_normalization_eval₂_eq_zero (g : S →+* R') (p : S[X])
  {x : R'} (hx : eval₂ g x p = 0) :
  eval₂ (g.comp (algebra_map R S)) x (integer_normalization M p) = 0 :=
let ⟨b, hb⟩ := integer_normalization_map_to_map M p in
trans (eval₂_map (algebra_map R S) g x).symm
  (by rw [hb, ← is_scalar_tower.algebra_map_smul S (b : R) p, eval₂_smul, hx, mul_zero])

lemma integer_normalization_aeval_eq_zero [algebra R R'] [algebra S R'] [is_scalar_tower R S R']
  (p : S[X]) {x : R'} (hx : aeval x p = 0) :
  aeval x (integer_normalization M p) = 0 :=
by rw [aeval_def, is_scalar_tower.algebra_map_eq R S R',
       integer_normalization_eval₂_eq_zero _ _ _ hx]

end integer_normalization
end is_localization

namespace is_fraction_ring

open is_localization

variables {A K C : Type*} [comm_ring A] [is_domain A] [field K] [algebra A K] [is_fraction_ring A K]
variables [comm_ring C]

lemma integer_normalization_eq_zero_iff {p : K[X]} :
  integer_normalization (non_zero_divisors A) p = 0 ↔ p = 0 :=
begin
  refine (polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm),
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integer_normalization_spec _ p,
  split; intros h i,
  { apply to_map_eq_zero_iff.mp,
    rw [hb i, h i],
    apply smul_zero,
    assumption },
  { have hi := h i,
    rw [polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, algebra.smul_def] at hi,
    apply or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi),
    intro h,
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero,
    exact to_map_eq_zero_iff.mp h }
end

variables (A K C)

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
lemma is_algebraic_iff [algebra A C] [algebra K C] [is_scalar_tower A K C] {x : C} :
  is_algebraic A x ↔ is_algebraic K x :=
begin
  split; rintros ⟨p, hp, px⟩,
  { refine ⟨p.map (algebra_map A K), λ h, hp (polynomial.ext (λ i, _)), _⟩,
    { have : algebra_map A K (p.coeff i) = 0 := trans (polynomial.coeff_map _ _).symm (by simp [h]),
      exact to_map_eq_zero_iff.mp this },
    { rwa is_scalar_tower.aeval_apply _ K at px } },
  { exact ⟨integer_normalization _ p,
           mt integer_normalization_eq_zero_iff.mp hp,
           integer_normalization_aeval_eq_zero _ p px⟩ },
end

variables {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
lemma comap_is_algebraic_iff [algebra A C] [algebra K C] [is_scalar_tower A K C] :
  algebra.is_algebraic A C ↔ algebra.is_algebraic K C :=
⟨λ h x, (is_algebraic_iff A K C).mp (h x), λ h x, (is_algebraic_iff A K C).mpr (h x)⟩

end is_fraction_ring

open is_localization

section is_integral
variables {R S} {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
variables [algebra R Rₘ] [is_localization M Rₘ]
variables [algebra S Sₘ] [is_localization (algebra.algebra_map_submonoid S M) Sₘ]

variables {S M}

open polynomial

lemma ring_hom.is_integral_elem_localization_at_leading_coeff
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : submonoid R)
  (hM : p.leading_coeff ∈ M) {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
  [algebra R Rₘ] [is_localization M Rₘ]
  [algebra S Sₘ] [is_localization (M.map f : submonoid S) Sₘ] :
  (map Sₘ f M.le_comap_map : Rₘ →+* _).is_integral_elem (algebra_map S Sₘ x) :=
begin
  by_cases triv : (1 : Rₘ) = 0,
  { exact ⟨0, ⟨trans leading_coeff_zero triv.symm, eval₂_zero _ _⟩⟩ },
  haveI : nontrivial Rₘ := nontrivial_of_ne 1 0 triv,
  obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.mp
    (map_units Rₘ ⟨p.leading_coeff, hM⟩),
  refine ⟨(p.map (algebra_map R Rₘ)) * C b, ⟨_, _⟩⟩,
  { refine monic_mul_C_of_leading_coeff_mul_eq_one _,
    rwa leading_coeff_map_of_leading_coeff_ne_zero (algebra_map R Rₘ),
    refine λ hfp, zero_ne_one (trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1) },
  { refine eval₂_mul_eq_zero_of_left _ _ _ _,
    erw [eval₂_map, is_localization.map_comp, ← hom_eval₂ _ f (algebra_map S Sₘ) x],
    exact trans (congr_arg (algebra_map S Sₘ) hf) (ring_hom.map_zero _) }
end

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leading_coeff {x : S} (p : R[X])
  (hp : aeval x p = 0) (hM : p.leading_coeff ∈ M) :
  (map Sₘ (algebra_map R S)
      (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
    : Rₘ →+* _).is_integral_elem (algebra_map S Sₘ x) :=
(algebra_map R S).is_integral_elem_localization_at_leading_coeff x p hp M hM

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem is_integral_localization (H : algebra.is_integral R S) :
  (map Sₘ (algebra_map R S)
    (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
    : Rₘ →+* _).is_integral :=
begin
  intro x,
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (algebra.algebra_map_submonoid S M) x,
  obtain ⟨v, hv⟩ := hu,
  obtain ⟨v', hv'⟩ := is_unit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩),
  refine @is_integral_of_is_integral_mul_unit Rₘ _ _ _
    (localization_algebra M S) x (algebra_map S Sₘ u) v' _ _,
  { replace hv' := congr_arg (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) hv',
    rw [ring_hom.map_mul, ring_hom.map_one, ← ring_hom.comp_apply _ (algebra_map R Rₘ)] at hv',
    erw is_localization.map_comp at hv',
    exact hv.2 ▸ hv' },
  { obtain ⟨p, hp⟩ := H s,
    exact hx.symm ▸ is_integral_localization_at_leading_coeff p hp.2 (hp.1.symm ▸ M.one_mem) }
end

lemma is_integral_localization' {R S : Type*} [comm_ring R] [comm_ring S]
  {f : R →+* S} (hf : f.is_integral) (M : submonoid R) :
  (map (localization (M.map (f : R →* S))) f M.le_comap_map : localization M →+* _).is_integral :=
@is_integral_localization R _ M S _ f.to_algebra _ _ _ _ _ _ _ _ hf

end is_integral

variables {A K : Type*} [comm_ring A] [is_domain A]

namespace is_integral_closure

variables (A) {L : Type*} [field K] [field L] [algebra A K] [algebra A L] [is_fraction_ring A K]
variables (C : Type*) [comm_ring C] [is_domain C] [algebra C L] [is_integral_closure C A L]
variables [algebra A C] [is_scalar_tower A C L]

open algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_algebraic (alg : is_algebraic A L)
  (inj : ∀ x, algebra_map A L x = 0 → x = 0) :
  is_fraction_ring C L :=
{ map_units := λ ⟨y, hy⟩,
    is_unit.mk0 _ (show algebra_map C L y ≠ 0, from λ h, mem_non_zero_divisors_iff_ne_zero.mp hy
      ((algebra_map C L).injective_iff.mp (algebra_map_injective C A L) _ h)),
  surj := λ z, let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj in
    ⟨⟨mk' C (x : L) x.2, algebra_map _ _ y,
        mem_non_zero_divisors_iff_ne_zero.mpr (λ h, hy (inj _
          (by rw [is_scalar_tower.algebra_map_apply A C L, h, ring_hom.map_zero])))⟩,
     by rw [set_like.coe_mk, algebra_map_mk', ← is_scalar_tower.algebra_map_apply A C L, hxy]⟩,
  eq_iff_exists := λ x y, ⟨λ h, ⟨1, by simpa using algebra_map_injective C A L h⟩, λ ⟨c, hc⟩,
    congr_arg (algebra_map _ L) (mul_right_cancel₀ (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc)⟩ }

variables (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_finite_extension [algebra K L] [is_scalar_tower A K L]
  [finite_dimensional K L] : is_fraction_ring C L :=
is_fraction_ring_of_algebraic A C
  (is_fraction_ring.comap_is_algebraic_iff.mpr (is_algebraic_of_finite K L))
  (λ x hx, is_fraction_ring.to_map_eq_zero_iff.mp ((algebra_map K L).map_eq_zero.mp $
    (is_scalar_tower.algebra_map_apply _ _ _ _).symm.trans hx))

end is_integral_closure

namespace integral_closure

variables {L : Type*} [field K] [field L] [algebra A K] [is_fraction_ring A K]

open algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_algebraic [algebra A L] (alg : is_algebraic A L)
  (inj : ∀ x, algebra_map A L x = 0 → x = 0) :
  is_fraction_ring (integral_closure A L) L :=
is_integral_closure.is_fraction_ring_of_algebraic A (integral_closure A L) alg inj

variables (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_finite_extension [algebra A L] [algebra K L]
  [is_scalar_tower A K L] [finite_dimensional K L] :
  is_fraction_ring (integral_closure A L) L :=
is_integral_closure.is_fraction_ring_of_finite_extension A K L (integral_closure A L)

end integral_closure

namespace is_fraction_ring

variables (R S K)

/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
lemma is_algebraic_iff' [field K] [is_domain R] [is_domain S] [algebra R K] [algebra S K]
  [no_zero_smul_divisors R K] [is_fraction_ring S K] [is_scalar_tower R S K] :
  algebra.is_algebraic R S ↔ algebra.is_algebraic R K :=
begin
  simp only [algebra.is_algebraic],
  split,
  { intros h x,
    rw [is_fraction_ring.is_algebraic_iff R (fraction_ring R) K, is_algebraic_iff_is_integral],
    obtain ⟨(a : S), b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x,
    obtain ⟨f, hf₁, hf₂⟩ := h b,
    rw [div_eq_mul_inv],
    refine is_integral_mul _ _,
    { rw [← is_algebraic_iff_is_integral],
      refine _root_.is_algebraic_of_larger_base_of_injective
        (no_zero_smul_divisors.algebra_map_injective R (fraction_ring R)) _,
      exact is_algebraic_algebra_map_of_is_algebraic (h a) },
    { rw [← is_algebraic_iff_is_integral],
      use (f.map (algebra_map R (fraction_ring R))).reverse,
      split,
      { rwa [ne.def, polynomial.reverse_eq_zero, ← polynomial.degree_eq_bot,
          polynomial.degree_map_eq_of_injective
            (no_zero_smul_divisors.algebra_map_injective R (fraction_ring R)),
          polynomial.degree_eq_bot]},
      { haveI : invertible (algebra_map S K b),
           from is_unit.invertible (is_unit_of_mem_non_zero_divisors
              (mem_non_zero_divisors_iff_ne_zero.2
                (λ h, non_zero_divisors.ne_zero ha
                    ((ring_hom.injective_iff (algebra_map S K)).1
                    (no_zero_smul_divisors.algebra_map_injective _ _) b h)))),
        rw [polynomial.aeval_def, ← inv_of_eq_inv, polynomial.eval₂_reverse_eq_zero_iff,
          polynomial.eval₂_map, ← is_scalar_tower.algebra_map_eq, ← polynomial.aeval_def,
          ← is_scalar_tower.algebra_map_aeval, hf₂, ring_hom.map_zero] } } },
  { intros h x,
    obtain ⟨f, hf₁, hf₂⟩ := h (algebra_map S K x),
    use [f, hf₁],
    rw [← is_scalar_tower.algebra_map_aeval] at hf₂,
    exact (algebra_map S K).injective_iff.1
      (no_zero_smul_divisors.algebra_map_injective _ _) _ hf₂ }
end

end is_fraction_ring
