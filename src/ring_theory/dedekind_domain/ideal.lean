/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import algebra.algebra.subalgebra.pointwise
import algebraic_geometry.prime_spectrum.noetherian
import ring_theory.dedekind_domain.basic
import ring_theory.fractional_ideal

/-!
# Dedekind domains and ideals

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

lemma mul_generator_self_inv {R₁ : Type*} [comm_ring R₁] [algebra R₁ K] [is_localization R₁⁰ K]
  (I : fractional_ideal R₁⁰ K) [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
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

@[simp] lemma inv_one : (1⁻¹ : fractional_ideal R₁⁰ K) = 1 :=
fractional_ideal.div_one

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
  is_dedekind_domain_inv A ↔
    (∀ I ≠ (⊥ : fractional_ideal A⁰ K), I * I⁻¹ = 1) :=
begin
  let h := fractional_ideal.map_equiv (fraction_ring.alg_equiv A K),
  refine h.to_equiv.forall_congr (λ I, _),
  rw ← h.to_equiv.apply_eq_iff_eq,
  simp
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

lemma integrally_closed : is_integrally_closed A :=
begin
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine ⟨λ x hx, _⟩,
  rw [← set.mem_range, ← algebra.mem_bot, ← subalgebra.mem_to_submodule, algebra.to_submodule_bot,
      ← coe_span_singleton A⁰ (1 : fraction_ring A), fractional_ideal.span_singleton_one,
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
  obtain ⟨Z₀, hZ₀⟩ := prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0,
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
    mt ((injective_iff_map_eq_zero _).mp (is_fraction_ring.injective A K) a) ha0,
  have hb0 : algebra_map A K b ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (is_fraction_ring.injective A K) b)
      (λ h, hbJ $ h.symm ▸ J.zero_mem),
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine ⟨algebra_map A K b * (algebra_map A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩,
  { exact (fractional_ideal.coe_to_fractional_ideal_ne_zero le_rfl).mpr hM0.ne' },
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
  { rw [hI1, coe_ideal_top, one_mul, fractional_ideal.inv_one] },
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
  { rw [hJ0, inv_zero'], exact fractional_ideal.zero_le _ },
  intros x hx,
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices : x ∈ integral_closure A K,
  { rwa [is_integrally_closed.integral_closure_eq_bot, algebra.mem_bot, set.mem_range,
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
  refine ⟨alg_hom.range (polynomial.aeval x : A[X] →ₐ[A] K),
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
  { exact mt ((injective_iff_map_eq_zero (algebra_map A K)).mp
      (is_fraction_ring.injective A K) _) ha },
  { exact fractional_ideal.coe_ideal_ne_zero_iff.mp (right_ne_zero_of_mul hne) }
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
by convert fractional_ideal.mul_right_le_iff hJ using 1; simp only [mul_comm]

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

noncomputable instance fractional_ideal.comm_group_with_zero :
  comm_group_with_zero (fractional_ideal A⁰ K) :=
{ inv := λ I, I⁻¹,
  inv_zero := inv_zero' _,
  div := (/),
  div_eq_mul_inv := fractional_ideal.div_eq_mul_inv,
  exists_pair_ne := ⟨0, 1, (coe_to_fractional_ideal_injective le_rfl).ne
    (by simpa using @zero_ne_one (ideal A) _ _)⟩,
  mul_inv_cancel := λ I, fractional_ideal.mul_inv_cancel,
  .. fractional_ideal.comm_semiring }

noncomputable instance ideal.cancel_comm_monoid_with_zero :
  cancel_comm_monoid_with_zero (ideal A) :=
function.injective.cancel_comm_monoid_with_zero (coe_ideal_hom A⁰ (fraction_ring A))
  coe_ideal_injective (ring_hom.map_zero _) (ring_hom.map_one _) (ring_hom.map_mul _)
  (ring_hom.map_pow _)

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

noncomputable instance ideal.normalization_monoid : normalization_monoid (ideal A) :=
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

lemma ideal.strict_anti_pow (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
  strict_anti ((^) I : ℕ → ideal A) :=
strict_anti_nat_of_succ_lt $ λ e, ideal.dvd_not_unit_iff_lt.mp
  ⟨pow_ne_zero _ hI0, I, mt is_unit_iff.mp hI1, pow_succ' I e⟩

lemma ideal.pow_lt_self (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) : I^e < I :=
by convert I.strict_anti_pow hI0 hI1 he; rw pow_one

lemma ideal.exists_mem_pow_not_mem_pow_succ (I : ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
  ∃ x ∈ I^e, x ∉ I^(e+1) :=
set_like.exists_of_lt (I.strict_anti_pow hI0 hI1 e.lt_succ_self)

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
  let I : fractional_ideal A⁰ K := fractional_ideal.span_finset A s f,
  have hI0 : I ≠ 0 := fractional_ideal.span_finset_ne_zero.mpr ⟨j, hjs, hjf⟩,
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

end is_dedekind_domain

section is_dedekind_domain

variables {T : Type*} [comm_ring T] [is_domain T] [is_dedekind_domain T] {I J : ideal T}
open_locale classical
open multiset unique_factorization_monoid ideal

lemma prod_normalized_factors_eq_self (hI : I ≠ ⊥) : (normalized_factors I).prod = I :=
associated_iff_eq.1 (normalized_factors_prod hI)

lemma normalized_factors_prod {α : multiset (ideal T)}
  (h : ∀ p ∈ α, prime p) : normalized_factors α.prod = α :=
by { simp_rw [← multiset.rel_eq, ← associated_eq_eq],
     exact prime_factors_unique (prime_of_normalized_factor) h
      (normalized_factors_prod (α.prod_ne_zero_of_prime h)) }

lemma count_le_of_ideal_ge {I J : ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : ideal T) :
  count K (normalized_factors J) ≤ count K (normalized_factors I) :=
le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1
  (dvd_iff_le.2 h)) _

lemma sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  I ⊔ J = (normalized_factors I ∩ normalized_factors J).prod :=
begin
  have H : normalized_factors (normalized_factors I ∩ normalized_factors J).prod =
    normalized_factors I ∩ normalized_factors J,
  { apply _root_.normalized_factors_prod,
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
      _root_.normalized_factors_prod, le_iff_count],
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
by rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, ← inf_eq_inter,
       normalized_factors_of_irreducible_pow hJ, normalize_eq J, repeat_inf, prod_repeat]

lemma irreducible_pow_sup_of_le (hJ : irreducible J) (n : ℕ)
  (hn : ↑n ≤ multiplicity J I) : J^n ⊔ I = J^n :=
begin
  by_cases hI : I = ⊥,
  { simp [*] at *, },
  rw [irreducible_pow_sup hI hJ, min_eq_right],
  rwa [multiplicity_eq_count_normalized_factors hJ hI, enat.coe_le_coe, normalize_eq J] at hn
end

lemma irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : irreducible J) (n : ℕ)
  (hn : multiplicity J I ≤ n) : J^n ⊔ I = J ^ (multiplicity J I).get (enat.dom_of_le_coe hn) :=
begin
  rw [irreducible_pow_sup hI hJ, min_eq_left],
  congr,
  { rw [← enat.coe_inj, enat.coe_get, multiplicity_eq_count_normalized_factors hJ hI,
    normalize_eq J] },
  { rwa [multiplicity_eq_count_normalized_factors hJ hI, enat.coe_le_coe, normalize_eq J]
      at hn }
end

end is_dedekind_domain

section height_one_spectrum

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `height_one_spectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible. -/

namespace is_dedekind_domain

variables [is_domain R] [is_dedekind_domain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint has_inhabited_instance unused_arguments]
structure height_one_spectrum :=
(as_ideal : ideal R)
(is_prime : as_ideal.is_prime)
(ne_bot   : as_ideal ≠ ⊥)

variables (v : height_one_spectrum R) {R}

lemma height_one_spectrum.prime (v : height_one_spectrum R) : prime v.as_ideal :=
ideal.prime_of_is_prime v.ne_bot v.is_prime

lemma height_one_spectrum.irreducible (v : height_one_spectrum R) :
  irreducible v.as_ideal :=
begin
  rw [unique_factorization_monoid.irreducible_iff_prime],
  apply v.prime,
end

lemma height_one_spectrum.associates_irreducible (v : height_one_spectrum R) :
  irreducible (associates.mk v.as_ideal) :=
begin
  rw [associates.irreducible_mk _],
  apply v.irreducible,
end

end is_dedekind_domain

end height_one_spectrum

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

lemma ideal.count_normalized_factors_eq {p x : ideal R} (hp0 : p ≠ ⊥) [hp : p.is_prime] {n : ℕ}
  (hle : x ≤ p^n) (hlt : ¬ (x ≤ p^(n+1))) :
  (normalized_factors x).count p = n :=
count_normalized_factors_eq ((ideal.prime_iff_is_prime hp0).mpr hp).irreducible (normalize_eq _)
  (ideal.dvd_iff_le.mpr hle) (mt ideal.le_of_dvd hlt)

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

end dedekind_domain

end chinese_remainder
