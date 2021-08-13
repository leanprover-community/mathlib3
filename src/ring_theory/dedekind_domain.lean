/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

local notation R`⁰`:9000 := non_zero_divisors R

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.integral_closure [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
λ p ne_bot prime, by exactI
  integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) infer_instance)

end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

-- See library note [lower instance priority]
attribute [instance, priority 100] is_dedekind_domain.is_noetherian_ring

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (K : Type*) [field K] [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain A ↔
    is_noetherian_ring A ∧ dimension_le_one A ∧ integral_closure A K = ⊥ :=
⟨λ ⟨hr, hd, hi⟩, ⟨hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv A K), hi, algebra.map_bot]⟩,
 λ ⟨hr, hd, hi⟩, ⟨hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv A K).symm, hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

section inverse

variables {R₁ : Type*} [integral_domain R₁] [algebra R₁ K] [is_fraction_ring R₁ K]
variables {I J : fractional_ideal R₁⁰ K}

noncomputable instance : has_inv (fractional_ideal R₁⁰ K) := ⟨λ I, 1 / I⟩

lemma inv_eq : I⁻¹ = 1 / I := rfl

lemma inv_zero' : (0 : fractional_ideal R₁⁰ K)⁻¹ = 0 := fractional_ideal.div_zero

lemma inv_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
J⁻¹ = ⟨(1 : fractional_ideal R₁⁰ K) / J, fractional_ideal.fractional_div_of_nonzero h⟩ :=
fractional_ideal.div_nonzero _

lemma coe_inv_of_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
  (↑J⁻¹ : submodule R₁ K) = is_localization.coe_submodule K ⊤ / J :=
by { rwa inv_nonzero _, refl, assumption }

variables {K}

lemma mem_inv_iff (hI : I ≠ 0) {x : K} :
  x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : fractional_ideal R₁⁰ K) :=
fractional_ideal.mem_div_iff_of_nonzero hI

lemma inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) :
  J⁻¹ ≤ I⁻¹ :=
λ x, by { simp only [mem_inv_iff hI, mem_inv_iff hJ], exact λ h y hy, h y (hIJ hy) }

lemma le_self_mul_inv {I : fractional_ideal R₁⁰ K} (hI : I ≤ (1 : fractional_ideal R₁⁰ K)) :
  I ≤ I * I⁻¹ :=
fractional_ideal.le_self_mul_one_div hI

variables (K)

lemma coe_ideal_le_self_mul_inv (I : ideal R₁) :
  (I : fractional_ideal R₁⁰ K) ≤ I * I⁻¹ :=
le_self_mul_inv fractional_ideal.coe_ideal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal R₁⁰ K) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := fractional_ideal.ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply fractional_ideal.mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (fractional_ideal.mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply fractional_ideal.mul_left_mono I,
  apply (fractional_ideal.le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact fractional_ideal.mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal R₁⁰ K} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa ← right_inverse_eq K I J hJ⟩

lemma mul_inv_cancel_iff_is_unit {I : fractional_ideal R₁⁰ K} :
  I * I⁻¹ = 1 ↔ is_unit I :=
(mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variables {K' : Type*} [field K'] [algebra R₁ K'] [is_fraction_ring R₁ K']

@[simp] lemma map_inv (I : fractional_ideal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
  (I⁻¹).map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ :=
by rw [inv_eq, fractional_ideal.map_div, fractional_ideal.map_one, inv_eq]

open submodule submodule.is_principal

@[simp] lemma span_singleton_inv (x : K) :
  (fractional_ideal.span_singleton R₁⁰ x)⁻¹ = fractional_ideal.span_singleton _ (x⁻¹) :=
fractional_ideal.one_div_span_singleton x

lemma mul_generator_self_inv (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  I * fractional_ideal.span_singleton _ (generator (I : submodule R₁ K))⁻¹ = 1 :=
begin
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw fractional_ideal.eq_span_singleton_of_principal I },
  rw [fractional_ideal.span_singleton_mul_span_singleton, mul_inv_cancel,
    fractional_ideal.span_singleton_one],
  intro generator_I_eq_zero,
  apply h,
  rw [fractional_ideal.eq_span_singleton_of_principal I, generator_I_eq_zero,
    fractional_ideal.span_singleton_zero]
end

lemma invertible_of_principal (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
(fractional_ideal.mul_div_self_cancel_iff).mpr
  ⟨fractional_ideal.span_singleton _ (generator (I : submodule R₁ K))⁻¹,
    mul_generator_self_inv _ I h⟩

lemma invertible_iff_generator_nonzero (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] :
  I * I⁻¹ = 1 ↔ generator (I : submodule R₁ K) ≠ 0 :=
begin
  split,
  { intros hI hg,
    apply fractional_ideal.ne_zero_of_mul_eq_one _ _ hI,
    rw [fractional_ideal.eq_span_singleton_of_principal I, hg,
        fractional_ideal.span_singleton_zero] },
  { intro hg,
    apply invertible_of_principal,
    rw [fractional_ideal.eq_span_singleton_of_principal I],
    intro hI,
    have := fractional_ideal.mem_span_singleton_self _ (generator (I : submodule R₁ K)),
    rw [hI, fractional_ideal.mem_zero_iff] at this,
    contradiction }
end

lemma is_principal_inv (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  submodule.is_principal (I⁻¹).1 :=
begin
  rw [fractional_ideal.val_eq_coe, fractional_ideal.is_principal_iff],
  use (generator (I : submodule R₁ K))⁻¹,
  have hI : I  * fractional_ideal.span_singleton _ ((generator (I : submodule R₁ K))⁻¹)  = 1,
  apply mul_generator_self_inv _ I h,
  exact (right_inverse_eq _ I (fractional_ideal.span_singleton _
    ((generator (I : submodule R₁ K))⁻¹)) hI).symm
end

@[simp] lemma fractional_ideal.one_inv : (1⁻¹ : fractional_ideal R₁⁰ K) = 1 :=
fractional_ideal.div_one

/--
A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.comm_cancel_monoid_with_zero`.
-/
def is_dedekind_domain_inv : Prop :=
∀ I ≠ (⊥ : fractional_ideal A⁰ (fraction_ring A)), I * I⁻¹ = 1

open fractional_ideal

variables {R A K}

lemma is_dedekind_domain_inv_iff [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain_inv A ↔
    (∀ I ≠ (⊥ : fractional_ideal A⁰ K), I * I⁻¹ = 1) :=
begin
  set h : fraction_ring A ≃ₐ[A] K := fraction_ring.alg_equiv A K,
  split; rintros hi I hI,
  { have := hi (fractional_ideal.map h.symm.to_alg_hom I)
               (fractional_ideal.map_ne_zero h.symm.to_alg_hom hI),
    convert congr_arg (fractional_ideal.map h.to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_symm_map, map_one,
                 fractional_ideal.map_mul, fractional_ideal.map_div, inv_eq] },
  { have := hi (fractional_ideal.map h.to_alg_hom I)
               (fractional_ideal.map_ne_zero h.to_alg_hom hI),
    convert congr_arg (fractional_ideal.map h.symm.to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_map_symm, map_one,
                 fractional_ideal.map_mul, fractional_ideal.map_div, inv_eq] },
end

lemma fractional_ideal.adjoin_integral_eq_one_of_is_unit [algebra A K] [is_fraction_ring A K]
  (x : K) (hx : is_integral A x) (hI : is_unit (adjoin_integral A⁰ x hx)) :
  adjoin_integral A⁰ x hx = 1 :=
begin
  set I := adjoin_integral A⁰ x hx,
  have mul_self : I * I = I,
  { apply fractional_ideal.coe_to_submodule_injective, simp },
  convert congr_arg (* I⁻¹) mul_self;
  simp only [(mul_inv_cancel_iff_is_unit K).mpr hI, mul_assoc, mul_one],
end

namespace is_dedekind_domain_inv

variables [algebra A K] [is_fraction_ring A K] (h : is_dedekind_domain_inv A)

include h

lemma mul_inv_eq_one {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : I * I⁻¹ = 1 :=
is_dedekind_domain_inv_iff.mp h I hI

lemma inv_mul_eq_one {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : I⁻¹ * I = 1 :=
(mul_comm _ _).trans (h.mul_inv_eq_one hI)

protected lemma is_unit {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : is_unit I :=
is_unit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)

lemma is_noetherian_ring : is_noetherian_ring A :=
begin
  refine is_noetherian_ring_iff.mpr ⟨λ (I : ideal A), _⟩,
  by_cases hI : I = ⊥,
  { rw hI, apply submodule.fg_bot },
  have hI : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI,
  exact I.fg_of_is_unit (is_fraction_ring.injective A (fraction_ring A)) (h.is_unit hI)
end

lemma integrally_closed : integral_closure A (fraction_ring A) = ⊥ :=
begin
  rw eq_bot_iff,
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  rintros x hx,
  rw [← subalgebra.mem_to_submodule, algebra.to_submodule_bot,
      ← coe_span_singleton A⁰ (1 : fraction_ring A), fractional_ideal.span_singleton_one,
      ← fractional_ideal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)],
  { exact mem_adjoin_integral_self A⁰ x hx },
  { exact λ h, one_ne_zero (eq_zero_iff.mp h 1 (subalgebra.one_mem _)) },
end

lemma dimension_le_one : dimension_le_one A :=
begin
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintros P P_ne hP,
  refine ideal.is_maximal_def.mpr ⟨hP.ne_top, λ M hM, _⟩,
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr P_ne,
  have M'_ne : (M : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr
      (lt_of_le_of_lt bot_le hM).ne',

  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices : (M⁻¹ * P : fractional_ideal A⁰ (fraction_ring A)) ≤ P,
  { rw [eq_top_iff, ← coe_ideal_le_coe_ideal (fraction_ring A), fractional_ideal.coe_ideal_top],
    calc (1 : fractional_ideal A⁰ (fraction_ring A)) = _ * _ * _ : _
    ... ≤ _ * _ : mul_right_mono (P⁻¹ * M : fractional_ideal A⁰ (fraction_ring A)) this
    ... = M : _,
    { rw [mul_assoc, ← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul, h.inv_mul_eq_one M'_ne] },
    { rw [← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul] },
    { apply_instance } },

  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebra_map _ _ y` for some `y`.
  intros x hx,
  have le_one : (M⁻¹ * P : fractional_ideal A⁰ (fraction_ring A)) ≤ 1,
  { rw [← h.inv_mul_eq_one M'_ne],
    exact fractional_ideal.mul_left_mono _ ((coe_ideal_le_coe_ideal (fraction_ring A)).mpr hM.le) },
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx),

  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := set_like.exists_of_lt hM,
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := fractional_ideal.mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx,
  rw [← ring_hom.map_mul, ← mul_assoc, h.mul_inv_eq_one M'_ne, one_mul] at zy_mem,
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coe_ideal A⁰).mp zy_mem,
  rw is_fraction_ring.injective A (fraction_ring A) zy_eq at hzy,
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coe_ideal_of_mem A⁰ (or.resolve_left (hP.mem_or_mem hzy) hzp)
end

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem is_dedekind_domain : is_dedekind_domain A :=
⟨h.is_noetherian_ring, h.dimension_le_one, h.integrally_closed⟩

end is_dedekind_domain_inv

variables [algebra A K] [is_fraction_ring A K]

/-- Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
lemma exists_multiset_prod_cons_le_and_prod_not_le [is_dedekind_domain A]
  (hNF : ¬ is_field A) {I M : ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.is_maximal] :
  ∃ (Z : multiset (prime_spectrum A)),
    (M ::ₘ (Z.map prime_spectrum.as_ideal)).prod ≤ I ∧
    ¬ (multiset.prod (Z.map prime_spectrum.as_ideal) ≤ I) :=
begin
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0,
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ := multiset.well_founded_lt.has_min
    (λ Z, (Z.map prime_spectrum.as_ideal).prod ≤ I ∧ (Z.map prime_spectrum.as_ideal).prod ≠ ⊥)
    ⟨Z₀, hZ₀⟩,
  have hZM : multiset.prod (Z.map prime_spectrum.as_ideal) ≤ M := le_trans hZI hIM,
  have hZ0 : Z ≠ 0, { rintro rfl, simpa [hM.ne_top] using hZM },
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM,
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ',
  letI := classical.dec_eq (ideal A),
  have := multiset.map_erase prime_spectrum.as_ideal subtype.coe_injective P Z,
  obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map prime_spectrum.as_ideal).prod ≠ ⊥,
  { rwa [ne.def, ← multiset.cons_erase hPZ', multiset.prod_cons, ideal.mul_eq_bot,
         not_or_distrib, ← this] at hprodZ },
  -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
  have hPM' := (is_dedekind_domain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM,
  tactic.unfreeze_local_instances,
  subst hPM',

  -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
  refine ⟨Z.erase P, _, _⟩,
  { convert hZI,
    rw [this, multiset.cons_erase hPZ'] },
  { refine λ h, h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ),
    exact hZP0 }
end

namespace fractional_ideal

lemma exists_not_mem_one_of_ne_bot [is_dedekind_domain A]
  (hNF : ¬ is_field A) {I : ideal A} (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
  ∃ x : K, x ∈ (I⁻¹ : fractional_ideal A⁰ K) ∧ x ∉ (1 : fractional_ideal A⁰ K) :=
begin
  -- WLOG, let `I` be maximal.
  suffices : ∀ {M : ideal A} (hM : M.is_maximal),
    ∃ x : K, x ∈ (M⁻¹ : fractional_ideal A⁰ K) ∧ x ∉ (1 : fractional_ideal A⁰ K),
  { obtain ⟨M, hM, hIM⟩ : ∃ (M : ideal A), is_maximal M ∧ I ≤ M := ideal.exists_le_maximal I hI1,
    resetI,
    have hM0 := (M.bot_lt_of_maximal hNF).ne',
    obtain ⟨x, hxM, hx1⟩ := this hM,
    refine ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩;
      apply fractional_ideal.coe_ideal_ne_zero; assumption },

  -- Let `a` be a nonzero element of `M` and `J` the ideal generated by `a`.
  intros M hM,
  resetI,
  obtain ⟨⟨a, haM⟩, ha0⟩ := submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF),
  replace ha0 : a ≠ 0 := subtype.coe_injective.ne ha0,
  let J : ideal A := ideal.span {a},
  have hJ0 : J ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp ha0,
  have hJM : J ≤ M := ideal.span_le.mpr (set.singleton_subset_iff.mpr haM),
  have hM0 : ⊥ < M := M.bot_lt_of_maximal hNF,

  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM,
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := set_like.not_le_iff_exists.mp hnle,
  have hnz_fa : algebra_map A K a ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) a) ha0,
  have hb0 : algebra_map A K b ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) b)
      (λ h, hbJ $ h.symm ▸ J.zero_mem),
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine ⟨algebra_map A K b * (algebra_map A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩,
  { exact (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl _)).mpr hM0.ne' },
  { rintro y₀ hy₀,
    obtain ⟨y, h_Iy, rfl⟩ := (fractional_ideal.mem_coe_ideal _).mp hy₀,
    rw [mul_comm, ← mul_assoc, ← ring_hom.map_mul],
    have h_yb : y * b ∈ J,
    { apply hle,
      rw multiset.prod_cons,
      exact submodule.smul_mem_smul h_Iy hbZ },
    rw ideal.mem_span_singleton' at h_yb,
    rcases h_yb with ⟨c, hc⟩,
    rw [← hc, ring_hom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_one],
    apply fractional_ideal.coe_mem_one },
  { refine mt (fractional_ideal.mem_one_iff _).mp _,
    rintros ⟨x', h₂_abs⟩,
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← ring_hom.map_mul] at h₂_abs,
    have := ideal.mem_span_singleton'.mpr ⟨x', is_fraction_ring.injective A K h₂_abs⟩,
    contradiction },
end

lemma one_mem_inv_coe_ideal {I : ideal A} (hI : I ≠ ⊥) :
  (1 : K) ∈ (I : fractional_ideal A⁰ K)⁻¹ :=
begin
  rw mem_inv_iff (fractional_ideal.coe_ideal_ne_zero hI),
  intros y hy,
  rw one_mul,
  exact coe_ideal_le_one hy,
  assumption
end

lemma mul_inv_cancel_of_le_one [h : is_dedekind_domain A]
  {I : ideal A} (hI0 : I ≠ ⊥) (hI : ((I * I⁻¹)⁻¹ : fractional_ideal A⁰ K) ≤ 1) :
  (I * I⁻¹ : fractional_ideal A⁰ K) = 1 :=
begin
  -- Handle a few trivial cases.
  by_cases hI1 : I = ⊤,
  { rw [hI1, coe_ideal_top, one_mul, fractional_ideal.one_inv] },
  by_cases hNF : is_field A,
  { letI := hNF.to_field A, rcases hI1 (I.eq_bot_or_top.resolve_left hI0) },
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  by_contradiction h_abs,
  obtain ⟨J, hJ⟩ : ∃ (J : ideal A), (J : fractional_ideal A⁰ K) = I * I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one,
  by_cases hJ0 : J = ⊥,
  { subst hJ0,
    apply hI0,
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ],
    exact coe_ideal_le_self_mul_inv K I,
    apply_instance },
  have hJ1 : J ≠ ⊤,
  { rintro rfl,
    rw [← hJ, coe_ideal_top] at h_abs,
    exact h_abs rfl },
  obtain ⟨x, hx, hx1⟩ : ∃ (x : K),
    x ∈ (J : fractional_ideal A⁰ K)⁻¹ ∧ x ∉ (1 : fractional_ideal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1,
  rw hJ at hx,
  exact hx1 (hI hx)
end

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
lemma coe_ideal_mul_inv [h : is_dedekind_domain A] (I : ideal A) (hI0 : I ≠ ⊥) :
  (I * I⁻¹ : fractional_ideal A⁰ K) = 1 :=
begin
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0,
  by_cases hJ0 : (I * I⁻¹ : fractional_ideal A⁰ K) = 0,
  { rw [hJ0, inv_zero'], exact fractional_ideal.zero_le _ },
  intros x hx,
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices : x ∈ integral_closure A K,
  { rwa [((is_dedekind_domain_iff _ _).mp h).2.2, algebra.mem_bot, set.mem_range,
         ← fractional_ideal.mem_one_iff] at this;
      assumption },
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw mem_integral_closure_iff_mem_fg,
  have x_mul_mem : ∀ b ∈ (I⁻¹ : fractional_ideal A⁰ K), x * b ∈ (I⁻¹ : fractional_ideal A⁰ K),
  { intros b hb,
    rw mem_inv_iff at ⊢ hx,
    swap, { exact fractional_ideal.coe_ideal_ne_zero hI0 },
    swap, { exact hJ0 },
    simp only [mul_assoc, mul_comm b] at ⊢ hx,
    intros y hy,
    exact hx _ (fractional_ideal.mul_mem_mul hy hb) },
  -- It turns out the subalgebra consisting of all `p(x)` for `p : polynomial A` works.
  refine ⟨alg_hom.range (polynomial.aeval x : polynomial A →ₐ[A] K),
          is_noetherian_submodule.mp (fractional_ideal.is_noetherian I⁻¹) _ (λ y hy, _),
          ⟨polynomial.X, polynomial.aeval_X x⟩⟩,
  obtain ⟨p, rfl⟩ := (alg_hom.mem_range _).mp hy,
  rw polynomial.aeval_eq_sum_range,
  refine submodule.sum_mem _ (λ i hi, submodule.smul_mem _ _ _),
  clear hi,
  induction i with i ih,
  { rw pow_zero, exact one_mem_inv_coe_ideal hI0 },
  { show x ^ i.succ ∈ (I⁻¹ : fractional_ideal A⁰ K),
    rw pow_succ, exact x_mul_mem _ ih },
end

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [is_dedekind_domain A]
  {I : fractional_ideal A⁰ K} (hne : I ≠ 0) : I * I⁻¹ = 1 :=
begin
  obtain ⟨a, J, ha, hJ⟩ :
    ∃ (a : A) (aI : ideal A), a ≠ 0 ∧ I = span_singleton A⁰ (algebra_map _ _ a)⁻¹ * aI :=
    exists_eq_span_singleton_mul I,
  suffices h₂ : I * (span_singleton A⁰ (algebra_map _ _ a) * J⁻¹) = 1,
  { rw mul_inv_cancel_iff,
    exact ⟨span_singleton A⁰ (algebra_map _ _ a) * J⁻¹, h₂⟩ },
  subst hJ,
  rw [mul_assoc, mul_left_comm (J : fractional_ideal A⁰ K), coe_ideal_mul_inv, mul_one,
      fractional_ideal.span_singleton_mul_span_singleton, inv_mul_cancel,
      fractional_ideal.span_singleton_one],
  { exact mt ((algebra_map A K).injective_iff.mp (is_fraction_ring.injective A K) _) ha },
  { exact fractional_ideal.coe_ideal_ne_zero_iff.mp (right_ne_zero_of_mul hne) }
end

end fractional_ideal

/-- `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem is_dedekind_domain_iff_is_dedekind_domain_inv :
  is_dedekind_domain A ↔ is_dedekind_domain_inv A :=
⟨λ h I hI, by exactI fractional_ideal.mul_inv_cancel hI, λ h, h.is_dedekind_domain⟩

end inverse

section is_dedekind_domain

variables {R A} [is_dedekind_domain A] [algebra A K] [is_fraction_ring A K]

open fractional_ideal

noncomputable instance fractional_ideal.comm_group_with_zero :
  comm_group_with_zero (fractional_ideal A⁰ K) :=
{ inv := λ I, I⁻¹,
  inv_zero := inv_zero' _,
  exists_pair_ne := ⟨0, 1, (coe_to_fractional_ideal_injective (le_refl _)).ne
    (by simpa using @zero_ne_one (ideal A) _ _)⟩,
  mul_inv_cancel := λ I, fractional_ideal.mul_inv_cancel,
  .. fractional_ideal.comm_semiring }

noncomputable instance ideal.comm_cancel_monoid_with_zero :
  comm_cancel_monoid_with_zero (ideal A) :=
function.injective.comm_cancel_monoid_with_zero (coe_ideal_hom A⁰ (fraction_ring A))
  coe_ideal_injective (ring_hom.map_zero _) (ring_hom.map_one _) (ring_hom.map_mul _)

/-- For ideals in a Dedekind domain, to divide is to contain. -/
lemma ideal.dvd_iff_le {I J : ideal A} : (I ∣ J) ↔ J ≤ I :=
⟨ideal.le_of_dvd,
  λ h, begin
    by_cases hI : I = ⊥,
    { have hJ : J = ⊥, { rwa [hI, ← eq_bot_iff] at h },
      rw [hI, hJ] },
    have hI' : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
      (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI,
    have : (I : fractional_ideal A⁰ (fraction_ring A))⁻¹ * J ≤ 1 := le_trans
      (fractional_ideal.mul_left_mono (↑I)⁻¹ ((coe_ideal_le_coe_ideal _).mpr h))
      (le_of_eq (inv_mul_cancel hI')),
    obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this,
    use H,
    refine coe_to_fractional_ideal_injective (le_refl (non_zero_divisors A))
      (show (J : fractional_ideal A⁰ (fraction_ring A)) = _, from _),
    rw [fractional_ideal.coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]
end⟩

lemma ideal.dvd_not_unit_iff_lt {I J : ideal A} :
  dvd_not_unit I J ↔ J < I :=
⟨λ ⟨hI, H, hunit, hmul⟩, lt_of_le_of_ne (ideal.dvd_iff_le.mp ⟨H, hmul⟩)
   (mt (λ h, have H = 1, from mul_left_cancel' hI (by rw [← hmul, h, mul_one]),
   show is_unit H, from this.symm ▸ is_unit_one) hunit),
 λ h, dvd_not_unit_of_dvd_of_not_dvd (ideal.dvd_iff_le.mpr (le_of_lt h))
   (mt ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

instance : wf_dvd_monoid (ideal A) :=
{ well_founded_dvd_not_unit :=
  have well_founded ((>) : ideal A → ideal A → Prop) :=
  is_noetherian_iff_well_founded.mp
    (is_noetherian_ring_iff.mp is_dedekind_domain.is_noetherian_ring),
  by { convert this, ext, rw ideal.dvd_not_unit_iff_lt } }

instance ideal.unique_factorization_monoid :
  unique_factorization_monoid (ideal A) :=
{ irreducible_iff_prime := λ P,
    ⟨λ hirr, ⟨hirr.ne_zero, hirr.not_unit, λ I J, begin
      have : P.is_maximal,
      { use mt ideal.is_unit_iff.mpr hirr.not_unit,
        intros J hJ,
        obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ,
        exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit) },
      simp only [ideal.dvd_iff_le, has_le.le, preorder.le, partial_order.le],
      contrapose!,
      rintros ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩,
      exact ⟨x * y, ideal.mul_mem_mul x_mem y_mem,
             mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩,
    end⟩,
     λ h, irreducible_of_prime h⟩,
  .. ideal.wf_dvd_monoid }

noncomputable instance ideal.normalization_monoid : normalization_monoid (ideal A) :=
normalization_monoid_of_unique_units

end is_dedekind_domain
