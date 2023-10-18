/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import algebra.algebra.subalgebra.pointwise
import algebraic_geometry.prime_spectrum.maximal
import algebraic_geometry.prime_spectrum.noetherian
import order.hom.basic
import ring_theory.dedekind_domain.basic
import ring_theory.fractional_ideal
import ring_theory.principal_ideal_domain
import ring_theory.chain_of_divisors

/-!
# Dedekind domains and ideals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible.
Then we prove some results on the unique factorization monoid structure of the ideals.

## Main definitions

 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.
 - `is_dedekind_domain.height_one_spectrum` defines the type of nonzero prime ideals of `R`.

## Main results:
 - `is_dedekind_domain_iff_is_dedekind_domain_inv`
 - `ideal.unique_factorization_monoid`

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

variables (R A K : Type*) [comm_ring R] [comm_ring A] [field K]

open_locale non_zero_divisors polynomial

variables [is_domain A]

section inverse

namespace fractional_ideal

variables {R₁ : Type*} [comm_ring R₁] [is_domain R₁] [algebra R₁ K] [is_fraction_ring R₁ K]
variables {I J : fractional_ideal R₁⁰ K}

noncomputable instance : has_inv (fractional_ideal R₁⁰ K) := ⟨λ I, 1 / I⟩

lemma inv_eq : I⁻¹ = 1 / I := rfl

lemma inv_zero' : (0 : fractional_ideal R₁⁰ K)⁻¹ = 0 := div_zero

lemma inv_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
J⁻¹ = ⟨(1 : fractional_ideal R₁⁰ K) / J, fractional_div_of_nonzero h⟩ := div_nonzero _

lemma coe_inv_of_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
  (↑J⁻¹ : submodule R₁ K) = is_localization.coe_submodule K ⊤ / J :=
by { rwa inv_nonzero _, refl, assumption }

variables {K}

lemma mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : fractional_ideal R₁⁰ K) :=
mem_div_iff_of_nonzero hI

lemma inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ :=
λ x, by { simp only [mem_inv_iff hI, mem_inv_iff hJ], exact λ h y hy, h y (hIJ hy) }

lemma le_self_mul_inv {I : fractional_ideal R₁⁰ K} (hI : I ≤ (1 : fractional_ideal R₁⁰ K)) :
  I ≤ I * I⁻¹ :=
le_self_mul_one_div hI

variables (K)

lemma coe_ideal_le_self_mul_inv (I : ideal R₁) : (I : fractional_ideal R₁⁰ K) ≤ I * I⁻¹ :=
le_self_mul_inv coe_ideal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply mul_left_mono I,
  apply (le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa ← right_inverse_eq K I J hJ⟩

lemma mul_inv_cancel_iff_is_unit {I : fractional_ideal R₁⁰ K} : I * I⁻¹ = 1 ↔ is_unit I :=
(mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variables {K' : Type*} [field K'] [algebra R₁ K'] [is_fraction_ring R₁ K']

@[simp] lemma map_inv (I : fractional_ideal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
  (I⁻¹).map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ :=
by rw [inv_eq, map_div, map_one, inv_eq]

open submodule submodule.is_principal

@[simp] lemma span_singleton_inv (x : K) : (span_singleton R₁⁰ x)⁻¹ = span_singleton _ x⁻¹ :=
one_div_span_singleton x

@[simp] lemma span_singleton_div_span_singleton (x y : K) :
  span_singleton R₁⁰ x / span_singleton R₁⁰ y = span_singleton R₁⁰ (x / y) :=
by rw [div_span_singleton, mul_comm, span_singleton_mul_span_singleton, div_eq_mul_inv]

lemma span_singleton_div_self {x : K} (hx : x ≠ 0) :
  span_singleton R₁⁰ x / span_singleton R₁⁰ x = 1 :=
by rw [span_singleton_div_span_singleton, div_self hx, span_singleton_one]

lemma coe_ideal_span_singleton_div_self {x : R₁} (hx : x ≠ 0) :
  (ideal.span ({x} : set R₁) : fractional_ideal R₁⁰ K) / ideal.span ({x} : set R₁) = 1 :=
by rw [coe_ideal_span_singleton, span_singleton_div_self K $
        (map_ne_zero_iff _ $ no_zero_smul_divisors.algebra_map_injective R₁ K).mpr hx]

lemma span_singleton_mul_inv {x : K} (hx : x ≠ 0) :
  span_singleton R₁⁰ x * (span_singleton R₁⁰ x)⁻¹ = 1 :=
by rw [span_singleton_inv, span_singleton_mul_span_singleton, mul_inv_cancel hx, span_singleton_one]

lemma coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x ≠ 0) :
  (ideal.span ({x} : set R₁) : fractional_ideal R₁⁰ K) * (ideal.span ({x} : set R₁))⁻¹ = 1 :=
by rw [coe_ideal_span_singleton, span_singleton_mul_inv K $
        (map_ne_zero_iff _ $ no_zero_smul_divisors.algebra_map_injective R₁ K).mpr hx]

lemma span_singleton_inv_mul {x : K} (hx : x ≠ 0) :
  (span_singleton R₁⁰ x)⁻¹ * span_singleton R₁⁰ x = 1 :=
by rw [mul_comm, span_singleton_mul_inv K hx]

lemma coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x ≠ 0) :
  (ideal.span ({x} : set R₁) : fractional_ideal R₁⁰ K)⁻¹ * ideal.span ({x} : set R₁) = 1 :=
by rw [mul_comm, coe_ideal_span_singleton_mul_inv K hx]

lemma mul_generator_self_inv {R₁ : Type*} [comm_ring R₁] [algebra R₁ K] [is_localization R₁⁰ K]
  (I : fractional_ideal R₁⁰ K) [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  I * span_singleton _ (generator (I : submodule R₁ K))⁻¹ = 1 :=
begin
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw eq_span_singleton_of_principal I },
  rw [span_singleton_mul_span_singleton, mul_inv_cancel, span_singleton_one],
  intro generator_I_eq_zero,
  apply h,
  rw [eq_span_singleton_of_principal I, generator_I_eq_zero, span_singleton_zero]
end

lemma invertible_of_principal (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) : I * I⁻¹ = 1 :=
(mul_div_self_cancel_iff).mpr
  ⟨span_singleton _ (generator (I : submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

lemma invertible_iff_generator_nonzero (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] :
  I * I⁻¹ = 1 ↔ generator (I : submodule R₁ K) ≠ 0 :=
begin
  split,
  { intros hI hg,
    apply ne_zero_of_mul_eq_one _ _ hI,
    rw [eq_span_singleton_of_principal I, hg, span_singleton_zero] },
  { intro hg,
    apply invertible_of_principal,
    rw [eq_span_singleton_of_principal I],
    intro hI,
    have := mem_span_singleton_self _ (generator (I : submodule R₁ K)),
    rw [hI, mem_zero_iff] at this,
    contradiction }
end

lemma is_principal_inv (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  submodule.is_principal (I⁻¹).1 :=
begin
  rw [val_eq_coe, is_principal_iff],
  use (generator (I : submodule R₁ K))⁻¹,
  have hI : I  * span_singleton _ ((generator (I : submodule R₁ K))⁻¹)  = 1,
  apply mul_generator_self_inv _ I h,
  exact (right_inverse_eq _ I (span_singleton _ ((generator (I : submodule R₁ K))⁻¹)) hI).symm
end

noncomputable instance : inv_one_class (fractional_ideal R₁⁰ K) :=
{ inv_one := div_one,
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_inv K }

end fractional_ideal

/--
A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.cancel_comm_monoid_with_zero`.
-/
def is_dedekind_domain_inv : Prop :=
∀ I ≠ (⊥ : fractional_ideal A⁰ (fraction_ring A)), I * I⁻¹ = 1

open fractional_ideal

variables {R A K}

lemma is_dedekind_domain_inv_iff [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain_inv A ↔ (∀ I ≠ (⊥ : fractional_ideal A⁰ K), I * I⁻¹ = 1) :=
begin
  let h := map_equiv (fraction_ring.alg_equiv A K),
  refine h.to_equiv.forall_congr (λ I, _),
  rw ← h.to_equiv.apply_eq_iff_eq,
  simp [is_dedekind_domain_inv, show ⇑h.to_equiv = h, from rfl],
end

lemma fractional_ideal.adjoin_integral_eq_one_of_is_unit [algebra A K] [is_fraction_ring A K]
  (x : K) (hx : is_integral A x) (hI : is_unit (adjoin_integral A⁰ x hx)) :
  adjoin_integral A⁰ x hx = 1 :=
begin
  set I := adjoin_integral A⁰ x hx,
  have mul_self : I * I = I,
  { apply coe_to_submodule_injective, simp },
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
  have hI : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 := coe_ideal_ne_zero.mpr hI,
  exact I.fg_of_is_unit (is_fraction_ring.injective A (fraction_ring A)) (h.is_unit hI)
end

lemma integrally_closed : is_integrally_closed A :=
begin
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine ⟨λ x hx, _⟩,
  rw [← set.mem_range, ← algebra.mem_bot, ← subalgebra.mem_to_submodule, algebra.to_submodule_bot,
      ← coe_span_singleton A⁰ (1 : fraction_ring A), span_singleton_one,
      ← fractional_ideal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)],
  { exact mem_adjoin_integral_self A⁰ x hx },
  { exact λ h, one_ne_zero (eq_zero_iff.mp h 1 (subalgebra.one_mem _)) },
end

open ring

lemma dimension_le_one : dimension_le_one A :=
begin
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintros P P_ne hP,
  refine ideal.is_maximal_def.mpr ⟨hP.ne_top, λ M hM, _⟩,
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 := coe_ideal_ne_zero.mpr P_ne,
  have M'_ne : (M : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    coe_ideal_ne_zero.mpr (lt_of_le_of_lt bot_le hM).ne',

  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices : (M⁻¹ * P : fractional_ideal A⁰ (fraction_ring A)) ≤ P,
  { rw [eq_top_iff, ← coe_ideal_le_coe_ideal (fraction_ring A), coe_ideal_top],
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
    exact mul_left_mono _ ((coe_ideal_le_coe_ideal (fraction_ring A)).mpr hM.le) },
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx),

  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := set_like.exists_of_lt hM,
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx,
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
  obtain ⟨Z₀, hZ₀⟩ := prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0,
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ := multiset.well_founded_lt.has_min
    (λ Z, (Z.map prime_spectrum.as_ideal).prod ≤ I ∧ (Z.map prime_spectrum.as_ideal).prod ≠ ⊥)
    ⟨Z₀, hZ₀⟩,
  have hZM : multiset.prod (Z.map prime_spectrum.as_ideal) ≤ M := le_trans hZI hIM,
  have hZ0 : Z ≠ 0, { rintro rfl, simpa [hM.ne_top] using hZM },
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM,
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ',
  classical,
  have := multiset.map_erase prime_spectrum.as_ideal prime_spectrum.ext P Z,
  obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map prime_spectrum.as_ideal).prod ≠ ⊥,
  { rwa [ne.def, ← multiset.cons_erase hPZ', multiset.prod_cons, ideal.mul_eq_bot,
         not_or_distrib, ← this] at hprodZ },
  -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
  have hPM' := (is_dedekind_domain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM,
  substI hPM',

  -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
  refine ⟨Z.erase P, _, _⟩,
  { convert hZI,
    rw [this, multiset.cons_erase hPZ'] },
  { refine λ h, h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ),
    exact hZP0 }
end

namespace fractional_ideal

open ideal

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
      rw coe_ideal_ne_zero; assumption },

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
    mt ((injective_iff_map_eq_zero _).mp (is_fraction_ring.injective A K) a) ha0,
  have hb0 : algebra_map A K b ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (is_fraction_ring.injective A K) b)
      (λ h, hbJ $ h.symm ▸ J.zero_mem),
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine ⟨algebra_map A K b * (algebra_map A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩,
  { exact coe_ideal_ne_zero.mpr hM0.ne' },
  { rintro y₀ hy₀,
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coe_ideal _).mp hy₀,
    rw [mul_comm, ← mul_assoc, ← ring_hom.map_mul],
    have h_yb : y * b ∈ J,
    { apply hle,
      rw multiset.prod_cons,
      exact submodule.smul_mem_smul h_Iy hbZ },
    rw ideal.mem_span_singleton' at h_yb,
    rcases h_yb with ⟨c, hc⟩,
    rw [← hc, ring_hom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_one],
    apply coe_mem_one },
  { refine mt (mem_one_iff _).mp _,
    rintros ⟨x', h₂_abs⟩,
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← ring_hom.map_mul] at h₂_abs,
    have := ideal.mem_span_singleton'.mpr ⟨x', is_fraction_ring.injective A K h₂_abs⟩,
    contradiction },
end

lemma one_mem_inv_coe_ideal {I : ideal A} (hI : I ≠ ⊥) :
  (1 : K) ∈ (I : fractional_ideal A⁰ K)⁻¹ :=
begin
  rw mem_inv_iff (coe_ideal_ne_zero.mpr hI),
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
  { rw [hI1, coe_ideal_top, one_mul, inv_one] },
  by_cases hNF : is_field A,
  { letI := hNF.to_field, rcases hI1 (I.eq_bot_or_top.resolve_left hI0) },
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ (J : ideal A), (J : fractional_ideal A⁰ K) = I * I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one,
  by_cases hJ0 : J = ⊥,
  { subst hJ0,
    refine absurd _ hI0,
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ],
    exact coe_ideal_le_self_mul_inv K I,
    apply_instance },
  by_cases hJ1 : J = ⊤,
  { rw [← hJ, hJ1, coe_ideal_top] },
  obtain ⟨x, hx, hx1⟩ : ∃ (x : K),
    x ∈ (J : fractional_ideal A⁰ K)⁻¹ ∧ x ∉ (1 : fractional_ideal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1,
  contrapose! hx1 with h_abs,
  rw hJ at hx,
  exact hI hx,
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
  { rw [hJ0, inv_zero'], exact zero_le _ },
  intros x hx,
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices : x ∈ integral_closure A K,
  { rwa [is_integrally_closed.integral_closure_eq_bot, algebra.mem_bot, set.mem_range,
         ← mem_one_iff] at this;
      assumption },
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw mem_integral_closure_iff_mem_fg,
  have x_mul_mem : ∀ b ∈ (I⁻¹ : fractional_ideal A⁰ K), x * b ∈ (I⁻¹ : fractional_ideal A⁰ K),
  { intros b hb,
    rw mem_inv_iff at ⊢ hx,
    swap, { exact coe_ideal_ne_zero.mpr hI0 },
    swap, { exact hJ0 },
    simp only [mul_assoc, mul_comm b] at ⊢ hx,
    intros y hy,
    exact hx _ (mul_mem_mul hy hb) },
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨alg_hom.range (polynomial.aeval x : A[X] →ₐ[A] K),
          is_noetherian_submodule.mp (is_noetherian I⁻¹) _ (λ y hy, _),
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
      span_singleton_mul_span_singleton, inv_mul_cancel, span_singleton_one],
  { exact mt ((injective_iff_map_eq_zero (algebra_map A K)).mp
      (is_fraction_ring.injective A K) _) ha },
  { exact coe_ideal_ne_zero.mp (right_ne_zero_of_mul hne) }
end

lemma mul_right_le_iff [is_dedekind_domain A] {J : fractional_ideal A⁰ K}
  (hJ : J ≠ 0) : ∀ {I I'}, I * J ≤ I' * J ↔ I ≤ I' :=
begin
  intros I I',
  split,
  { intros h, convert mul_right_mono J⁻¹ h;
      rw [mul_assoc, fractional_ideal.mul_inv_cancel hJ, mul_one] },
  { exact λ h, mul_right_mono J h }
end

lemma mul_left_le_iff [is_dedekind_domain A] {J : fractional_ideal A⁰ K}
  (hJ : J ≠ 0) {I I'} : J * I ≤ J * I' ↔ I ≤ I' :=
by convert mul_right_le_iff hJ using 1; simp only [mul_comm]

lemma mul_right_strict_mono [is_dedekind_domain A] {I : fractional_ideal A⁰ K}
  (hI : I ≠ 0) : strict_mono (* I) :=
strict_mono_of_le_iff_le (λ _ _, (mul_right_le_iff hI).symm)

lemma mul_left_strict_mono [is_dedekind_domain A] {I : fractional_ideal A⁰ K}
  (hI : I ≠ 0) : strict_mono ((*) I) :=
strict_mono_of_le_iff_le (λ _ _, (mul_left_le_iff hI).symm)

/--
This is also available as `_root_.div_eq_mul_inv`, using the
`comm_group_with_zero` instance defined below.
-/
protected lemma div_eq_mul_inv [is_dedekind_domain A] (I J : fractional_ideal A⁰ K) :
  I / J = I * J⁻¹ :=
begin
  by_cases hJ : J = 0,
  { rw [hJ, div_zero, inv_zero', mul_zero] },
  refine le_antisymm ((mul_right_le_iff hJ).mp _) ((le_div_iff_mul_le hJ).mpr _),
  { rw [mul_assoc, mul_comm J⁻¹, fractional_ideal.mul_inv_cancel hJ, mul_one, mul_le],
    intros x hx y hy,
    rw [mem_div_iff_of_nonzero hJ] at hx,
    exact hx y hy },
  rw [mul_assoc, mul_comm J⁻¹, fractional_ideal.mul_inv_cancel hJ, mul_one],
  exact le_refl I
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
open ideal

noncomputable instance fractional_ideal.semifield :
  semifield (fractional_ideal A⁰ K) :=
{ inv := λ I, I⁻¹,
  inv_zero := inv_zero' _,
  div := (/),
  div_eq_mul_inv := fractional_ideal.div_eq_mul_inv,
  mul_inv_cancel := λ I, fractional_ideal.mul_inv_cancel,
  .. fractional_ideal.comm_semiring, .. coe_ideal_injective.nontrivial }

/-- Fractional ideals have cancellative multiplication in a Dedekind domain.

Although this instance is a direct consequence of the instance
`fractional_ideal.comm_group_with_zero`, we define this instance to provide
a computable alternative.
-/
instance fractional_ideal.cancel_comm_monoid_with_zero :
  cancel_comm_monoid_with_zero (fractional_ideal A⁰ K) :=
{ .. fractional_ideal.comm_semiring, -- Project out the computable fields first.
  .. (by apply_instance : cancel_comm_monoid_with_zero (fractional_ideal A⁰ K)) }

instance ideal.cancel_comm_monoid_with_zero :
  cancel_comm_monoid_with_zero (ideal A) :=
{ .. ideal.idem_comm_semiring,
  .. function.injective.cancel_comm_monoid_with_zero (coe_ideal_hom A⁰ (fraction_ring A))
    coe_ideal_injective (ring_hom.map_zero _) (ring_hom.map_one _) (ring_hom.map_mul _)
    (ring_hom.map_pow _) }

instance ideal.is_domain :
  is_domain (ideal A) :=
{ .. (infer_instance : is_cancel_mul_zero _), .. ideal.nontrivial }

/-- For ideals in a Dedekind domain, to divide is to contain. -/
lemma ideal.dvd_iff_le {I J : ideal A} : (I ∣ J) ↔ J ≤ I :=
⟨ideal.le_of_dvd,
  λ h, begin
    by_cases hI : I = ⊥,
    { have hJ : J = ⊥, { rwa [hI, ← eq_bot_iff] at h },
      rw [hI, hJ] },
    have hI' : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 := coe_ideal_ne_zero.mpr hI,
    have : (I : fractional_ideal A⁰ (fraction_ring A))⁻¹ * J ≤ 1 := le_trans
      (mul_left_mono (↑I)⁻¹ ((coe_ideal_le_coe_ideal _).mpr h))
      (le_of_eq (inv_mul_cancel hI')),
    obtain ⟨H, hH⟩ := le_one_iff_exists_coe_ideal.mp this,
    use H,
    refine coe_ideal_injective
      (show (J : fractional_ideal A⁰ (fraction_ring A)) = ↑(I * H), from _),
    rw [coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]
end⟩

lemma ideal.dvd_not_unit_iff_lt {I J : ideal A} :
  dvd_not_unit I J ↔ J < I :=
⟨λ ⟨hI, H, hunit, hmul⟩, lt_of_le_of_ne (ideal.dvd_iff_le.mp ⟨H, hmul⟩)
   (mt (λ h, have H = 1, from mul_left_cancel₀ hI (by rw [← hmul, h, mul_one]),
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
    { refine ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩,
      intros J hJ,
      obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ,
      exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit) },
    rw [ideal.dvd_iff_le, ideal.dvd_iff_le, ideal.dvd_iff_le,
        set_like.le_def, set_like.le_def, set_like.le_def],
    contrapose!,
    rintros ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩,
    exact ⟨x * y, ideal.mul_mem_mul x_mem y_mem,
           mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩,
   end⟩,
   prime.irreducible⟩,
  .. ideal.wf_dvd_monoid }

instance ideal.normalization_monoid : normalization_monoid (ideal A) :=
normalization_monoid_of_unique_units

@[simp] lemma ideal.dvd_span_singleton {I : ideal A} {x : A} :
  I ∣ ideal.span {x} ↔ x ∈ I :=
ideal.dvd_iff_le.trans (ideal.span_le.trans set.singleton_subset_iff)

lemma ideal.is_prime_of_prime {P : ideal A} (h : prime P) : is_prime P :=
begin
  refine ⟨_, λ x y hxy, _⟩,
  { unfreezingI { rintro rfl },
    rw ← ideal.one_eq_top at h,
    exact h.not_unit is_unit_one },
  { simp only [← ideal.dvd_span_singleton, ← ideal.span_singleton_mul_span_singleton] at ⊢ hxy,
    exact h.dvd_or_dvd hxy }
end

theorem ideal.prime_of_is_prime {P : ideal A} (hP : P ≠ ⊥) (h : is_prime P) : prime P :=
begin
  refine ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, λ I J hIJ, _⟩,
  simpa only [ideal.dvd_iff_le] using (h.mul_le.mp (ideal.le_of_dvd hIJ)),
end

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
are exactly the prime ideals. -/
theorem ideal.prime_iff_is_prime {P : ideal A} (hP : P ≠ ⊥) :
  prime P ↔ is_prime P :=
⟨ideal.is_prime_of_prime, ideal.prime_of_is_prime hP⟩

/-- In a Dedekind domain, the the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `ideal A`. -/
theorem ideal.is_prime_iff_bot_or_prime {P : ideal A} :
  is_prime P ↔ P = ⊥ ∨ prime P :=
⟨λ hp, (eq_or_ne P ⊥).imp_right $ λ hp0, (ideal.prime_of_is_prime hp0 hp),
 λ hp, hp.elim (λ h, h.symm ▸ ideal.bot_prime) ideal.is_prime_of_prime⟩

lemma ideal.strict_anti_pow (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
  strict_anti ((^) I : ℕ → ideal A) :=
strict_anti_nat_of_succ_lt $ λ e, ideal.dvd_not_unit_iff_lt.mp
  ⟨pow_ne_zero _ hI0, I, mt is_unit_iff.mp hI1, pow_succ' I e⟩

lemma ideal.pow_lt_self (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) : I^e < I :=
by convert I.strict_anti_pow hI0 hI1 he; rw pow_one

lemma ideal.exists_mem_pow_not_mem_pow_succ (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
  ∃ x ∈ I^e, x ∉ I^(e+1) :=
set_like.exists_of_lt (I.strict_anti_pow hI0 hI1 e.lt_succ_self)

open unique_factorization_monoid

lemma ideal.eq_prime_pow_of_succ_lt_of_le {P I : ideal A} [P_prime : P.is_prime] (hP : P ≠ ⊥)
  {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) :
  I = P ^ i :=
begin
  letI := classical.dec_eq (ideal A),
  refine le_antisymm hle _,
  have P_prime' := ideal.prime_of_is_prime hP P_prime,
  have : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne',
  have := pow_ne_zero i hP,
  have := pow_ne_zero (i + 1) hP,
  rw [← ideal.dvd_not_unit_iff_lt, dvd_not_unit_iff_normalized_factors_lt_normalized_factors,
      normalized_factors_pow, normalized_factors_irreducible P_prime'.irreducible,
      multiset.nsmul_singleton, multiset.lt_replicate_succ]
    at hlt,
  rw [← ideal.dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors, normalized_factors_pow,
      normalized_factors_irreducible P_prime'.irreducible, multiset.nsmul_singleton],
  all_goals { assumption }
end

lemma ideal.pow_succ_lt_pow {P : ideal A} [P_prime : P.is_prime] (hP : P ≠ ⊥)
  (i : ℕ) :
  P ^ (i + 1) < P ^ i :=
lt_of_le_of_ne (ideal.pow_le_pow (nat.le_succ _))
  (mt (pow_eq_pow_iff hP (mt ideal.is_unit_iff.mp P_prime.ne_top)).mp i.succ_ne_self)

lemma associates.le_singleton_iff (x : A) (n : ℕ) (I : ideal A) :
  associates.mk I^n ≤ associates.mk (ideal.span {x}) ↔ x ∈ I^n :=
begin
  rw [← associates.dvd_eq_le, ← associates.mk_pow, associates.mk_dvd_mk, ideal.dvd_span_singleton],
end

open fractional_ideal
variables {A K}

/-- Strengthening of `is_localization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
lemma ideal.exist_integer_multiples_not_mem
  {J : ideal A} (hJ : J ≠ ⊤) {ι : Type*} (s : finset ι) (f : ι → K)
  {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
  ∃ a : K, (∀ i ∈ s, is_localization.is_integer A (a * f i)) ∧
    ∃ i ∈ s, (a * f i) ∉ (J : fractional_ideal A⁰ K) :=
begin
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : fractional_ideal A⁰ K := span_finset A s f,
  have hI0 : I ≠ 0 := span_finset_ne_zero.mpr ⟨j, hjs, hjf⟩,
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices : ↑J / I < I⁻¹,
  { obtain ⟨_, a, hI, hpI⟩ := set_like.lt_iff_le_and_exists.mp this,
    rw mem_inv_iff hI0 at hI,
    refine ⟨a, λ i hi, _, _⟩,
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    { exact (mem_one_iff _).mp (hI (f i)
        (submodule.subset_span (set.mem_image_of_mem f hi))) },
    { contrapose! hpI,
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine (mem_div_iff_of_nonzero hI0).mpr (λ y hy, submodule.span_induction hy _ _ _ _),
      { rintros _ ⟨i, hi, rfl⟩, exact hpI i hi },
      { rw mul_zero, exact submodule.zero_mem _ },
      { intros x y hx hy, rw mul_add, exact submodule.add_mem _ hx hy },
      { intros b x hx, rw mul_smul_comm, exact submodule.smul_mem _ b hx } } },
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  calc ↑J / I = ↑J * I⁻¹ : div_eq_mul_inv ↑J I
          ... < 1 * I⁻¹ : mul_right_strict_mono (inv_ne_zero hI0) _
          ... = I⁻¹ : one_mul _,
  { rw [← coe_ideal_top],
    -- And multiplying by `I⁻¹` is indeed strictly monotone.
    exact strict_mono_of_le_iff_le (λ _ _, (coe_ideal_le_coe_ideal K).symm)
      (lt_top_iff_ne_top.mpr hJ) },
end

section gcd

namespace ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `normalized_gcd_monoid (ideal A)`.
-/

@[simp] lemma sup_mul_inf (I J : ideal A) : (I ⊔ J) * (I ⊓ J) = I * J :=
begin
  letI := classical.dec_eq (ideal A),
  letI := classical.dec_eq (associates (ideal A)),
  letI := unique_factorization_monoid.to_normalized_gcd_monoid (ideal A),
  have hgcd : gcd I J = I ⊔ J,
  { rw [gcd_eq_normalize _ _, normalize_eq],
    { rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le],
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩ },
    { rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le],
      simp } },
  have hlcm : lcm I J = I ⊓ J,
  { rw [lcm_eq_normalize _ _, normalize_eq],
    { rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le],
      simp },
    { rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le],
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩ } },
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)],
  apply_instance
end

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
instance : normalized_gcd_monoid (ideal A) :=
{ gcd := (⊔),
  gcd_dvd_left := λ _ _, by simpa only [dvd_iff_le] using le_sup_left,
  gcd_dvd_right := λ _ _, by simpa only [dvd_iff_le] using le_sup_right,
  dvd_gcd := λ _ _ _, by simpa only [dvd_iff_le] using sup_le,
  lcm := (⊓),
  lcm_zero_left := λ _, by simp only [zero_eq_bot, bot_inf_eq],
  lcm_zero_right := λ _, by simp only [zero_eq_bot, inf_bot_eq],
  gcd_mul_lcm := λ _ _, by rw [associated_iff_eq, sup_mul_inf],
  normalize_gcd := λ _ _, normalize_eq _,
  normalize_lcm := λ _ _, normalize_eq _,
  .. ideal.normalization_monoid }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp] lemma gcd_eq_sup (I J : ideal A) : gcd I J = I ⊔ J := rfl

@[simp]
lemma lcm_eq_inf (I J : ideal A) : lcm I J = I ⊓ J := rfl

lemma inf_eq_mul_of_coprime {I J : ideal A} (coprime : I ⊔ J = ⊤) :
  I ⊓ J = I * J :=
by rw [← associated_iff_eq.mp (gcd_mul_lcm I J), lcm_eq_inf I J, gcd_eq_sup, coprime, top_mul]

end ideal

end gcd

end is_dedekind_domain

section is_dedekind_domain

variables {T : Type*} [comm_ring T] [is_domain T] [is_dedekind_domain T] {I J : ideal T}
open_locale classical
open multiset unique_factorization_monoid ideal

lemma prod_normalized_factors_eq_self (hI : I ≠ ⊥) : (normalized_factors I).prod = I :=
associated_iff_eq.1 (normalized_factors_prod hI)

lemma count_le_of_ideal_ge {I J : ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : ideal T) :
  count K (normalized_factors J) ≤ count K (normalized_factors I) :=
le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1
  (dvd_iff_le.2 h)) _

lemma sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  I ⊔ J = (normalized_factors I ∩ normalized_factors J).prod :=
begin
  have H : normalized_factors (normalized_factors I ∩ normalized_factors J).prod =
    normalized_factors I ∩ normalized_factors J,
  { apply normalized_factors_prod_of_prime,
    intros p hp,
    rw mem_inter at hp,
    exact prime_of_normalized_factor p hp.left },
  have := (multiset.prod_ne_zero_of_prime (normalized_factors I ∩ normalized_factors J)
      (λ _ h, prime_of_normalized_factor _ (multiset.mem_inter.1 h).1)),
  apply le_antisymm,
  { rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le],
    split,
    { rw [dvd_iff_normalized_factors_le_normalized_factors this hI, H],
      exact inf_le_left },
    { rw [dvd_iff_normalized_factors_le_normalized_factors this hJ, H],
      exact inf_le_right } },
  { rw [← dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors,
      normalized_factors_prod_of_prime, le_iff_count],
    { intro a,
      rw multiset.count_inter,
      exact le_min (count_le_of_ideal_ge le_sup_left hI a)
        (count_le_of_ideal_ge le_sup_right hJ a) },
    { intros p hp,
      rw mem_inter at hp,
      exact prime_of_normalized_factor p hp.left },
    { exact ne_bot_of_le_ne_bot hI le_sup_left },
    { exact this } },
end

lemma irreducible_pow_sup (hI : I ≠ ⊥) (hJ : irreducible J) (n : ℕ) :
  J^n ⊔ I = J^(min ((normalized_factors I).count J) n) :=
by rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, min_comm,
       normalized_factors_of_irreducible_pow hJ, normalize_eq J, replicate_inter, prod_replicate]

lemma irreducible_pow_sup_of_le (hJ : irreducible J) (n : ℕ)
  (hn : ↑n ≤ multiplicity J I) : J^n ⊔ I = J^n :=
begin
  by_cases hI : I = ⊥,
  { simp [*] at *, },
  rw [irreducible_pow_sup hI hJ, min_eq_right],
  rwa [multiplicity_eq_count_normalized_factors hJ hI, part_enat.coe_le_coe, normalize_eq J] at hn
end

lemma irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : irreducible J) (n : ℕ)
  (hn : multiplicity J I ≤ n) : J^n ⊔ I = J ^ (multiplicity J I).get (part_enat.dom_of_le_coe hn) :=
begin
  rw [irreducible_pow_sup hI hJ, min_eq_left],
  congr,
  { rw [← part_enat.coe_inj, part_enat.coe_get, multiplicity_eq_count_normalized_factors hJ hI,
    normalize_eq J] },
  { rwa [multiplicity_eq_count_normalized_factors hJ hI, part_enat.coe_le_coe, normalize_eq J]
      at hn }
end

end is_dedekind_domain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `height_one_spectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/

namespace is_dedekind_domain

variables [is_domain R] [is_dedekind_domain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint has_nonempty_instance unused_arguments]
structure height_one_spectrum :=
(as_ideal : ideal R)
(is_prime : as_ideal.is_prime)
(ne_bot : as_ideal ≠ ⊥)

attribute [instance] height_one_spectrum.is_prime

variables (v : height_one_spectrum R) {R}

namespace height_one_spectrum

instance is_maximal : v.as_ideal.is_maximal := dimension_le_one v.as_ideal v.ne_bot v.is_prime

lemma prime : prime v.as_ideal := ideal.prime_of_is_prime v.ne_bot v.is_prime

lemma irreducible : irreducible v.as_ideal :=
unique_factorization_monoid.irreducible_iff_prime.mpr v.prime

lemma associates_irreducible : _root_.irreducible $ associates.mk v.as_ideal :=
(associates.irreducible_mk _).mpr v.irreducible

/-- An equivalence between the height one and maximal spectra for rings of Krull dimension 1. -/
def equiv_maximal_spectrum (hR : ¬is_field R) : height_one_spectrum R ≃ maximal_spectrum R :=
{ to_fun    := λ v, ⟨v.as_ideal, dimension_le_one v.as_ideal v.ne_bot v.is_prime⟩,
  inv_fun   := λ v,
    ⟨v.as_ideal, v.is_maximal.is_prime, ring.ne_bot_of_is_maximal_of_not_is_field v.is_maximal hR⟩,
  left_inv  := λ ⟨_, _, _⟩, rfl,
  right_inv := λ ⟨_, _⟩, rfl }

variables (R K)

/-- A Dedekind domain is equal to the intersection of its localizations at all its height one
non-zero prime ideals viewed as subalgebras of its field of fractions. -/
theorem infi_localization_eq_bot [algebra R K] [hK : is_fraction_ring R K] :
  (⨅ v : height_one_spectrum R,
    localization.subalgebra.of_field K _ v.as_ideal.prime_compl_le_non_zero_divisors) = ⊥ :=
begin
  ext x,
  rw [algebra.mem_infi],
  split,
  by_cases hR : is_field R,
  { rcases function.bijective_iff_has_inverse.mp
      (is_field.localization_map_bijective (flip non_zero_divisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩,
    exact λ _, algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩,
    exact hK },
  all_goals { rw [← maximal_spectrum.infi_localization_eq_bot, algebra.mem_infi] },
  { exact λ hx ⟨v, hv⟩, hx ((equiv_maximal_spectrum hR).symm ⟨v, hv⟩) },
  { exact λ hx ⟨v, hv, hbot⟩, hx ⟨v, dimension_le_one v hbot hv⟩ }
end

end height_one_spectrum

end is_dedekind_domain

section

open ideal

variables {R} {A} [is_dedekind_domain A] {I : ideal R} {J : ideal A}

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
def ideal_factors_fun_of_quot_hom {f : R ⧸ I →+* A ⧸ J} (hf : function.surjective f ) :
  {p : ideal R | p ∣ I} →o {p : ideal A | p ∣ J} :=
{ to_fun := λ X, ⟨comap J^.quotient.mk (map f (map I^.quotient.mk X)),
    begin
      have : (J^.quotient.mk).ker ≤ comap J^.quotient.mk (map f (map I^.quotient.mk X)),
      { exact ker_le_comap J^.quotient.mk },
      rw mk_ker at this,
      exact dvd_iff_le.mpr this,
    end ⟩,
  monotone' :=
    begin
      rintros ⟨X, hX⟩ ⟨Y, hY⟩ h,
      rw [← subtype.coe_le_coe, subtype.coe_mk, subtype.coe_mk] at h ⊢,
      rw [subtype.coe_mk, comap_le_comap_iff_of_surjective J^.quotient.mk quotient.mk_surjective,
        map_le_iff_le_comap, subtype.coe_mk, comap_map_of_surjective _ hf (map I^.quotient.mk Y)],
      suffices : map I^.quotient.mk X ≤ map I^.quotient.mk Y,
      { exact le_sup_of_le_left this },
      rwa [map_le_iff_le_comap, comap_map_of_surjective I^.quotient.mk quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_eq_left.mpr $ le_of_dvd hY],
    end }

@[simp]
lemma ideal_factors_fun_of_quot_hom_id :
  ideal_factors_fun_of_quot_hom  (ring_hom.id (A ⧸ J)).is_surjective = order_hom.id :=
order_hom.ext _ _ (funext $ λ X, by simp only [ideal_factors_fun_of_quot_hom, map_id,
  order_hom.coe_fun_mk, order_hom.id_coe, id.def, comap_map_of_surjective J^.quotient.mk
  quotient.mk_surjective, ← ring_hom.ker_eq_comap_bot J^.quotient.mk, mk_ker, sup_eq_left.mpr
  (dvd_iff_le.mp X.prop), subtype.coe_eta] )

variables {B : Type*} [comm_ring B] [is_domain B] [is_dedekind_domain B] {L : ideal B}

lemma ideal_factors_fun_of_quot_hom_comp {f : R ⧸ I →+* A ⧸ J}  {g : A ⧸ J →+* B ⧸ L}
  (hf : function.surjective f) (hg : function.surjective g) :
  (ideal_factors_fun_of_quot_hom hg).comp (ideal_factors_fun_of_quot_hom hf)
    = ideal_factors_fun_of_quot_hom (show function.surjective (g.comp f), from hg.comp hf) :=
begin
  refine order_hom.ext _ _ (funext $ λ x, _),
  rw [ideal_factors_fun_of_quot_hom, ideal_factors_fun_of_quot_hom, order_hom.comp_coe,
    order_hom.coe_fun_mk, order_hom.coe_fun_mk, function.comp_app,
    ideal_factors_fun_of_quot_hom,  order_hom.coe_fun_mk, subtype.mk_eq_mk, subtype.coe_mk,
    map_comap_of_surjective J^.quotient.mk quotient.mk_surjective, map_map],
end

variables [is_domain R] [is_dedekind_domain R] (f : R ⧸ I ≃+* A ⧸ J)

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
@[simps]
def ideal_factors_equiv_of_quot_equiv : {p : ideal R | p ∣ I} ≃o {p : ideal A | p ∣ J} :=
order_iso.of_hom_inv
  (ideal_factors_fun_of_quot_hom (show function.surjective
    (f : R ⧸I →+* A ⧸ J), from f.surjective))
    (ideal_factors_fun_of_quot_hom (show function.surjective
    (f.symm : A ⧸J →+* R ⧸ I), from f.symm.surjective))
  (by simp only [← ideal_factors_fun_of_quot_hom_id, order_hom.coe_eq, order_hom.coe_eq,
    ideal_factors_fun_of_quot_hom_comp, ← ring_equiv.to_ring_hom_eq_coe,
    ← ring_equiv.to_ring_hom_eq_coe, ← ring_equiv.to_ring_hom_trans, ring_equiv.symm_trans_self,
    ring_equiv.to_ring_hom_refl])
  (by simp only [← ideal_factors_fun_of_quot_hom_id, order_hom.coe_eq, order_hom.coe_eq,
    ideal_factors_fun_of_quot_hom_comp, ← ring_equiv.to_ring_hom_eq_coe,
    ← ring_equiv.to_ring_hom_eq_coe, ← ring_equiv.to_ring_hom_trans, ring_equiv.self_trans_symm,
    ring_equiv.to_ring_hom_refl])

lemma ideal_factors_equiv_of_quot_equiv_symm :
  (ideal_factors_equiv_of_quot_equiv f).symm = ideal_factors_equiv_of_quot_equiv f.symm := rfl

lemma ideal_factors_equiv_of_quot_equiv_is_dvd_iso {L M : ideal R} (hL : L ∣ I) (hM : M ∣ I) :
  (ideal_factors_equiv_of_quot_equiv f ⟨L, hL⟩ : ideal A) ∣
    ideal_factors_equiv_of_quot_equiv f ⟨M, hM⟩  ↔ L ∣ M :=
begin
  suffices : ideal_factors_equiv_of_quot_equiv f ⟨M, hM⟩ ≤
    ideal_factors_equiv_of_quot_equiv f ⟨L, hL⟩ ↔ (⟨M, hM⟩ : {p : ideal R | p ∣ I}) ≤ ⟨L, hL⟩,
  { rw [dvd_iff_le, dvd_iff_le, subtype.coe_le_coe, this, subtype.mk_le_mk] },
  exact (ideal_factors_equiv_of_quot_equiv f).le_iff_le,
end

open unique_factorization_monoid

variables [decidable_eq (ideal R)] [decidable_eq (ideal A)]

lemma ideal_factors_equiv_of_quot_equiv_mem_normalized_factors_of_mem_normalized_factors
  (hJ : J ≠ ⊥) {L : ideal R} (hL : L ∈ normalized_factors I) :
  ↑(ideal_factors_equiv_of_quot_equiv f
    ⟨L, dvd_of_mem_normalized_factors hL⟩) ∈ normalized_factors J :=
begin
  by_cases hI : I = ⊥,
  { exfalso,
    rw [hI, bot_eq_zero, normalized_factors_zero, ← multiset.empty_eq_zero] at hL,
    exact hL, },
  { apply mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors hI hJ hL _,
    rintros ⟨l, hl⟩ ⟨l', hl'⟩,
    rw [subtype.coe_mk, subtype.coe_mk],
    apply ideal_factors_equiv_of_quot_equiv_is_dvd_iso f }
end

/-- The bijection between the sets of normalized factors of I and J induced by a ring
    isomorphism `f : R/I ≅ A/J`. -/
@[simps apply]
def normalized_factors_equiv_of_quot_equiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  {L : ideal R | L ∈ normalized_factors I } ≃ {M : ideal A | M ∈ normalized_factors J } :=
{ to_fun := λ j, ⟨ideal_factors_equiv_of_quot_equiv f ⟨↑j, dvd_of_mem_normalized_factors j.prop⟩,
   ideal_factors_equiv_of_quot_equiv_mem_normalized_factors_of_mem_normalized_factors f hJ j.prop⟩,
  inv_fun := λ j, ⟨(ideal_factors_equiv_of_quot_equiv f).symm
    ⟨↑j, dvd_of_mem_normalized_factors j.prop⟩, by { rw ideal_factors_equiv_of_quot_equiv_symm,
      exact ideal_factors_equiv_of_quot_equiv_mem_normalized_factors_of_mem_normalized_factors
        f.symm hI j.prop} ⟩,
  left_inv := λ ⟨j, hj⟩, by simp,
  right_inv := λ ⟨j, hj⟩, by simp }

@[simp]
lemma normalized_factors_equiv_of_quot_equiv_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  (normalized_factors_equiv_of_quot_equiv f hI hJ).symm =
    normalized_factors_equiv_of_quot_equiv f.symm hJ hI :=
rfl

variable [decidable_rel ((∣) : ideal R → ideal R → Prop)]
variable [decidable_rel ((∣) : ideal A → ideal A → Prop)]

/-- The map `normalized_factors_equiv_of_quot_equiv` preserves multiplicities. -/
lemma normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
  (L : ideal R) (hL : L ∈ normalized_factors I) :
  multiplicity ↑(normalized_factors_equiv_of_quot_equiv f hI hJ ⟨L, hL⟩) J = multiplicity L I :=
begin
  rw [normalized_factors_equiv_of_quot_equiv, equiv.coe_fn_mk, subtype.coe_mk],
  exact multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalized_factor hI hJ hL
    (λ ⟨l, hl⟩ ⟨l', hl'⟩, ideal_factors_equiv_of_quot_equiv_is_dvd_iso f hl hl'),
end

end

section chinese_remainder

open ideal unique_factorization_monoid
open_locale big_operators

variables {R}

lemma ring.dimension_le_one.prime_le_prime_iff_eq (h : ring.dimension_le_one R)
  {P Q : ideal R} [hP : P.is_prime] [hQ : Q.is_prime] (hP0 : P ≠ ⊥) :
  P ≤ Q ↔ P = Q :=
⟨(h P hP0 hP).eq_of_le hQ.ne_top, eq.le⟩

lemma ideal.coprime_of_no_prime_ge {I J : ideal R} (h : ∀ P, I ≤ P → J ≤ P → ¬ is_prime P) :
  I ⊔ J = ⊤ :=
begin
  by_contra hIJ,
  obtain ⟨P, hP, hIJ⟩ := ideal.exists_le_maximal _ hIJ,
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.is_prime
end

section dedekind_domain

variables {R} [is_domain R] [is_dedekind_domain R]

lemma ideal.is_prime.mul_mem_pow (I : ideal R) [hI : I.is_prime] {a b : R} {n : ℕ}
  (h : a * b ∈ I^n) : a ∈ I ∨ b ∈ I^n :=
begin
  cases n, { simp },
  by_cases hI0 : I = ⊥, { simpa [pow_succ, hI0] using h },
  simp only [← submodule.span_singleton_le_iff_mem, ideal.submodule_span_eq, ← ideal.dvd_iff_le,
    ← ideal.span_singleton_mul_span_singleton] at h ⊢,
  by_cases ha : I ∣ span {a},
  { exact or.inl ha },
  rw mul_comm at h,
  exact or.inr (prime.pow_dvd_of_dvd_mul_right ((ideal.prime_iff_is_prime hI0).mpr hI) _ ha h),
end

section

open_locale classical

lemma ideal.count_normalized_factors_eq {p x : ideal R} [hp : p.is_prime] {n : ℕ}
  (hle : x ≤ p^n) (hlt : ¬ (x ≤ p^(n+1))) :
  (normalized_factors x).count p = n :=
count_normalized_factors_eq'
  ((ideal.is_prime_iff_bot_or_prime.mp hp).imp_right prime.irreducible)
  (by { haveI : unique (ideal R)ˣ := ideal.unique_units, apply normalize_eq })
  (by convert ideal.dvd_iff_le.mpr hle) (by convert mt ideal.le_of_dvd hlt)
/- Warning: even though a pure term-mode proof typechecks (the `by convert` can simply be
  removed), it's slower to the point of a possible timeout. -/

end

lemma ideal.le_mul_of_no_prime_factors
  {I J K : ideal R} (coprime : ∀ P, J ≤ P → K ≤ P → ¬ is_prime P) (hJ : I ≤ J) (hK : I ≤ K) :
  I ≤ J * K :=
begin
  simp only [← ideal.dvd_iff_le] at coprime hJ hK ⊢,
  by_cases hJ0 : J = 0,
  { simpa only [hJ0, zero_mul] using hJ },
  obtain ⟨I', rfl⟩ := hK,
  rw mul_comm,
  exact mul_dvd_mul_left K
    (unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_factors hJ0
      (λ P hPJ hPK, mt ideal.is_prime_of_prime (coprime P hPJ hPK))
      hJ)
end

lemma ideal.le_of_pow_le_prime {I P : ideal R} [hP : P.is_prime] {n : ℕ} (h : I^n ≤ P) : I ≤ P :=
begin
  by_cases hP0 : P = ⊥,
  { simp only [hP0, le_bot_iff] at ⊢ h,
    exact pow_eq_zero h },
  rw ← ideal.dvd_iff_le at ⊢ h,
  exact ((ideal.prime_iff_is_prime hP0).mpr hP).dvd_of_dvd_pow h
end

lemma ideal.pow_le_prime_iff {I P : ideal R} [hP : P.is_prime] {n : ℕ} (hn : n ≠ 0) :
  I^n ≤ P ↔ I ≤ P :=
⟨ideal.le_of_pow_le_prime, λ h, trans (ideal.pow_le_self hn) h⟩

lemma ideal.prod_le_prime {ι : Type*} {s : finset ι} {f : ι → ideal R} {P : ideal R}
  [hP : P.is_prime] :
  ∏ i in s, f i ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
begin
  by_cases hP0 : P = ⊥,
  { simp only [hP0, le_bot_iff],
    rw [← ideal.zero_eq_bot, finset.prod_eq_zero_iff] },
  simp only [← ideal.dvd_iff_le],
  exact ((ideal.prime_iff_is_prime hP0).mpr hP).dvd_finset_prod_iff _
end

/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
lemma is_dedekind_domain.inf_prime_pow_eq_prod {ι : Type*}
  (s : finset ι) (f : ι → ideal R) (e : ι → ℕ)
  (prime : ∀ i ∈ s, prime (f i)) (coprime : ∀ i j ∈ s, i ≠ j → f i ≠ f j) :
  s.inf (λ i, f i ^ e i) = ∏ i in s, f i ^ e i :=
begin
  letI := classical.dec_eq ι,
  revert prime coprime,
  refine s.induction _ _,
  { simp },
  intros a s ha ih prime coprime,
  specialize ih (λ i hi, prime i (finset.mem_insert_of_mem hi))
    (λ i hi j hj, coprime i (finset.mem_insert_of_mem hi) j (finset.mem_insert_of_mem hj)),
  rw [finset.inf_insert, finset.prod_insert ha, ih],
  refine le_antisymm (ideal.le_mul_of_no_prime_factors _ inf_le_left inf_le_right) ideal.mul_le_inf,
  intros P hPa hPs hPp,
  haveI := hPp,
  obtain ⟨b, hb, hPb⟩ := ideal.prod_le_prime.mp hPs,
  haveI := ideal.is_prime_of_prime (prime a (finset.mem_insert_self a s)),
  haveI := ideal.is_prime_of_prime (prime b (finset.mem_insert_of_mem hb)),
  refine coprime a (finset.mem_insert_self a s) b (finset.mem_insert_of_mem hb) _
    (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp
        (ideal.le_of_pow_le_prime hPa)).trans
      ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp
        (ideal.le_of_pow_le_prime hPb)).symm),
  { unfreezingI { rintro rfl }, contradiction },
  { exact (prime a (finset.mem_insert_self a s)).ne_zero },
  { exact (prime b (finset.mem_insert_of_mem hb)).ne_zero },
end

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def is_dedekind_domain.quotient_equiv_pi_of_prod_eq {ι : Type*} [fintype ι]
  (I : ideal R) (P : ι → ideal R) (e : ι → ℕ)
  (prime : ∀ i, prime (P i)) (coprime : ∀ i j, i ≠ j → P i ≠ P j) (prod_eq : (∏ i, P i ^ e i) = I) :
  R ⧸ I ≃+* Π i, R ⧸ (P i ^ e i) :=
(ideal.quot_equiv_of_eq (by { simp only [← prod_eq, finset.inf_eq_infi, finset.mem_univ, cinfi_pos,
  ← is_dedekind_domain.inf_prime_pow_eq_prod _ _ _ (λ i _, prime i) (λ i _ j _, coprime i j)] }))
    .trans $
ideal.quotient_inf_ring_equiv_pi_quotient _ (λ i j hij, ideal.coprime_of_no_prime_ge (begin
  intros P hPi hPj hPp,
  haveI := hPp,
  haveI := ideal.is_prime_of_prime (prime i), haveI := ideal.is_prime_of_prime (prime j),
  exact coprime i j hij
    (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (prime i).ne_zero).mp
      (ideal.le_of_pow_le_prime hPi)).trans
    ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (prime j).ne_zero).mp
     (ideal.le_of_pow_le_prime hPj)).symm)
end))

open_locale classical

/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
noncomputable def is_dedekind_domain.quotient_equiv_pi_factors {I : ideal R} (hI : I ≠ ⊥) :
  R ⧸ I ≃+* Π (P : (factors I).to_finset), R ⧸ ((P : ideal R) ^ (factors I).count P) :=
is_dedekind_domain.quotient_equiv_pi_of_prod_eq _ _ _
  (λ (P : (factors I).to_finset), prime_of_factor _ (multiset.mem_to_finset.mp P.prop))
  (λ i j hij, subtype.coe_injective.ne hij)
  (calc ∏ (P : (factors I).to_finset), (P : ideal R) ^ (factors I).count (P : ideal R)
      = ∏ P in (factors I).to_finset, P ^ (factors I).count P
    : (factors I).to_finset.prod_coe_sort (λ P, P ^ (factors I).count P)
  ... = ((factors I).map (λ P, P)).prod : (finset.prod_multiset_map_count (factors I) id).symm
  ... = (factors I).prod : by rw multiset.map_id'
  ... = I : (@associated_iff_eq (ideal R) _ ideal.unique_units _ _).mp (factors_prod hI))

@[simp] lemma is_dedekind_domain.quotient_equiv_pi_factors_mk {I : ideal R} (hI : I ≠ ⊥)
  (x : R) : is_dedekind_domain.quotient_equiv_pi_factors hI (ideal.quotient.mk I x) =
    λ P, ideal.quotient.mk _ x :=
rfl

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def ideal.quotient_mul_equiv_quotient_prod (I J : ideal R)
  (coprime : I ⊔ J = ⊤) :
  (R ⧸ (I * J)) ≃+* (R ⧸ I) × R ⧸ J :=
ring_equiv.trans
  (ideal.quot_equiv_of_eq (inf_eq_mul_of_coprime coprime).symm)
  (ideal.quotient_inf_equiv_quotient_prod I J coprime)

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i in s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `is_dedekind_domain.quotient_equiv_pi_of_prod_eq` where we restrict
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
noncomputable def is_dedekind_domain.quotient_equiv_pi_of_finset_prod_eq {ι : Type*} {s : finset ι}
  (I : ideal R) (P : ι → ideal R) (e : ι → ℕ)
  (prime : ∀ i ∈ s, prime (P i)) (coprime : ∀ (i j ∈ s), i ≠ j → P i ≠ P j)
  (prod_eq : (∏ i in s, P i ^ e i) = I) :
  R ⧸ I ≃+* Π (i : s), R ⧸ (P i ^ e i) :=
is_dedekind_domain.quotient_equiv_pi_of_prod_eq I (λ (i : s), P i) (λ (i : s), e i)
  (λ i, prime i i.2)
  (λ i j h, coprime i i.2 j j.2 (subtype.coe_injective.ne h))
  (trans (finset.prod_coe_sort s (λ i, P i ^ e i)) prod_eq)

/-- Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`.-/
lemma is_dedekind_domain.exists_representative_mod_finset {ι : Type*} {s : finset ι}
  (P : ι → ideal R) (e : ι → ℕ)
  (prime : ∀ i ∈ s, prime (P i)) (coprime : ∀ (i j ∈ s), i ≠ j → P i ≠ P j)
  (x : Π (i : s), R ⧸ (P i ^ e i)) :
  ∃ y, ∀ i (hi : i ∈ s), ideal.quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ :=
begin
  let f := is_dedekind_domain.quotient_equiv_pi_of_finset_prod_eq _ P e prime coprime rfl,
  obtain ⟨y, rfl⟩ := f.surjective x,
  obtain ⟨z, rfl⟩ := ideal.quotient.mk_surjective y,
  exact ⟨z, λ i hi, rfl⟩
end

/-- Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`.-/
lemma is_dedekind_domain.exists_forall_sub_mem_ideal {ι : Type*} {s : finset ι}
  (P : ι → ideal R) (e : ι → ℕ)
  (prime : ∀ i ∈ s, prime (P i)) (coprime : ∀ (i j ∈ s), i ≠ j → P i ≠ P j)
  (x : s → R) :
  ∃ y, ∀ i (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i :=
begin
  obtain ⟨y, hy⟩ := is_dedekind_domain.exists_representative_mod_finset P e prime coprime
    (λ i, ideal.quotient.mk _ (x i)),
  exact ⟨y, λ i hi, ideal.quotient.eq.mp (hy i hi)⟩
end

end dedekind_domain

end chinese_remainder

section PID

open multiplicity unique_factorization_monoid ideal

variables {R} [is_domain R] [is_principal_ideal_ring R]

lemma span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
  (ideal.span {a}) ∣ (ideal.span ({b} : set R)) ↔ a ∣ b :=
⟨λ h, mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))),
  λ h, dvd_iff_le.mpr (λ d hd, mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd)))⟩

lemma singleton_span_mem_normalized_factors_of_mem_normalized_factors [normalization_monoid R]
  [decidable_eq R] [decidable_eq (ideal R)] {a b : R} (ha : a ∈ normalized_factors b) :
  ideal.span ({a} : set R) ∈ normalized_factors (ideal.span ({b} : set R)) :=
begin
  by_cases hb : b = 0,
  { rw [ideal.span_singleton_eq_bot.mpr hb, bot_eq_zero, normalized_factors_zero],
    rw [hb, normalized_factors_zero] at ha,
    simpa only [multiset.not_mem_zero] },
  { suffices : prime (ideal.span ({a} : set R)),
    { obtain ⟨c, hc, hc'⟩ := exists_mem_normalized_factors_of_dvd _ this.irreducible
        (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalized_factors ha))),
      rwa associated_iff_eq.mp hc',
      { by_contra,
        exact hb (span_singleton_eq_bot.mp h) } },
    rw prime_iff_is_prime,
    exact (span_singleton_prime (prime_of_normalized_factor a ha).ne_zero).mpr
      (prime_of_normalized_factor a ha),
    by_contra,
    exact (prime_of_normalized_factor a ha).ne_zero (span_singleton_eq_bot.mp h) },
end

lemma multiplicity_eq_multiplicity_span [decidable_rel ((∣) : R → R → Prop)]
  [decidable_rel ((∣) : ideal R → ideal R → Prop)] {a b : R} :
  multiplicity (ideal.span {a}) (ideal.span ({b} : set R)) = multiplicity a b :=
begin
  by_cases h : finite a b,
    { rw ← part_enat.coe_get (finite_iff_dom.mp h),
      refine (multiplicity.unique
        (show (ideal.span {a})^(((multiplicity a b).get h)) ∣ (ideal.span {b}), from _) _).symm ;
        rw [ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd],
      exact pow_multiplicity_dvd h ,
      { exact multiplicity.is_greatest ((part_enat.lt_coe_iff _ _).mpr (exists.intro
          (finite_iff_dom.mp h) (nat.lt_succ_self _))) } },
    { suffices : ¬ (finite (ideal.span ({a} : set R)) (ideal.span ({b} : set R))),
      { rw [finite_iff_dom, part_enat.not_dom_iff_eq_top] at h this,
        rw [h, this] },
      refine not_finite_iff_forall.mpr (λ n, by {rw [ideal.span_singleton_pow,
        span_singleton_dvd_span_singleton_iff_dvd], exact not_finite_iff_forall.mp h n }) }
end

variables [decidable_eq R] [decidable_eq (ideal R)] [normalization_monoid R]

/-- The bijection between the (normalized) prime factors of `r` and the (normalized) prime factors
    of `span {r}` -/
@[simps]
noncomputable def normalized_factors_equiv_span_normalized_factors {r : R} (hr : r ≠ 0) :
  {d : R | d ∈ normalized_factors r} ≃
    {I : ideal R | I ∈ normalized_factors (ideal.span ({r} : set R))} :=
equiv.of_bijective
  (λ d, ⟨ideal.span {↑d}, singleton_span_mem_normalized_factors_of_mem_normalized_factors d.prop⟩)
begin
  split,
  { rintros ⟨a, ha⟩ ⟨b, hb⟩ h,
    rw [subtype.mk_eq_mk, ideal.span_singleton_eq_span_singleton, subtype.coe_mk,
      subtype.coe_mk] at h,
    exact subtype.mk_eq_mk.mpr (mem_normalized_factors_eq_of_associated ha hb h) },
  { rintros ⟨i, hi⟩,
    letI : i.is_principal := infer_instance,
    letI : i.is_prime := is_prime_of_prime (prime_of_normalized_factor i hi),
    obtain ⟨a, ha, ha'⟩ := exists_mem_normalized_factors_of_dvd hr
      (submodule.is_principal.prime_generator_of_is_prime i
        (prime_of_normalized_factor i hi).ne_zero).irreducible _,
    { use ⟨a, ha⟩,
      simp only [subtype.coe_mk, subtype.mk_eq_mk, ← span_singleton_eq_span_singleton.mpr ha',
        ideal.span_singleton_generator] },
    {exact (submodule.is_principal.mem_iff_generator_dvd i).mp (((show ideal.span {r} ≤ i, from
      dvd_iff_le.mp (dvd_of_mem_normalized_factors hi))) (mem_span_singleton.mpr (dvd_refl r))) } }
end

variables [decidable_rel ((∣) : R → R → Prop)] [decidable_rel ((∣) : ideal R → ideal R → Prop)]

/-- The bijection `normalized_factors_equiv_span_normalized_factors` between the set of prime
    factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multiplicities. -/
lemma multiplicity_normalized_factors_equiv_span_normalized_factors_eq_multiplicity {r d: R}
  (hr : r ≠ 0) (hd : d ∈ normalized_factors r) :
  multiplicity d r =
    multiplicity (normalized_factors_equiv_span_normalized_factors hr ⟨d, hd⟩ : ideal R)
      (ideal.span {r}) :=
by simp only [normalized_factors_equiv_span_normalized_factors, multiplicity_eq_multiplicity_span,
    subtype.coe_mk, equiv.of_bijective_apply]

/-- The bijection `normalized_factors_equiv_span_normalized_factors.symm` between the set of prime
    factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multiplicities. -/
lemma multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity
  {r : R} (hr : r ≠ 0) (I : {I : ideal R | I ∈ normalized_factors (ideal.span ({r} : set R))}) :
  multiplicity ((normalized_factors_equiv_span_normalized_factors hr).symm I : R) r =
    multiplicity (I : ideal R) (ideal.span {r}) :=
begin
  obtain ⟨x, hx⟩ := (normalized_factors_equiv_span_normalized_factors hr).surjective I,
  obtain ⟨a, ha⟩ := x,
  rw [hx.symm, equiv.symm_apply_apply, subtype.coe_mk,
    multiplicity_normalized_factors_equiv_span_normalized_factors_eq_multiplicity hr ha, hx],
end

end PID
