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

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is not a field,
   Noetherian, integrally closed in its field of fractions and has Krull dimension exactly one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is not a field, Noetherian, and the localization at every nonzero prime ideal is a DVR.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain that
   is not a field, and every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

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
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end
end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (f : fraction_map A K) :
  is_dedekind_domain A ↔
    (¬ is_field A) ∧ is_noetherian_ring A ∧ dimension_le_one A ∧
    integral_closure A f.codomain = ⊥ :=
⟨λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f),
         hi, algebra.map_bot]⟩,
 λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f).symm,
         hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

section inverse

open_locale classical

variables {R₁ : Type*} [integral_domain R₁] {g : fraction_map R₁ K}
variables {I J : fractional_ideal g}

noncomputable instance : has_inv (fractional_ideal g) := ⟨λ I, 1 / I⟩

lemma inv_eq : I⁻¹ = 1 / I := rfl

lemma inv_zero' : (0 : fractional_ideal g)⁻¹ = 0 := fractional_ideal.div_zero

lemma inv_nonzero {J : fractional_ideal g} (h : J ≠ 0) :
J⁻¹ = ⟨(1 : fractional_ideal g) / J, fractional_ideal.fractional_div_of_nonzero h⟩ :=
fractional_ideal.div_nonzero _

lemma coe_inv_of_nonzero {J : fractional_ideal g} (h : J ≠ 0) :
  (↑J⁻¹ : submodule R₁ g.codomain) = g.coe_submodule 1 / J :=
by { rwa inv_nonzero _, refl, assumption}

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal g) (h : I * J = 1) :
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

theorem mul_inv_cancel_iff {I : fractional_ideal g} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa [← @right_inverse_eq _ _ _ _ _ I J hJ]⟩

variables {K' : Type*} [field K'] {g' : fraction_map R₁ K'}

@[simp] lemma map_inv (I : fractional_ideal g) (h : g.codomain ≃ₐ[R₁] g'.codomain) :
  (I⁻¹).map (h : g.codomain →ₐ[R₁] g'.codomain) = (I.map h)⁻¹ :=
by rw [inv_eq, fractional_ideal.map_div, fractional_ideal.map_one, inv_eq]

open_locale classical

open submodule submodule.is_principal

@[simp] lemma span_singleton_inv (x : g.codomain) :
  (fractional_ideal.span_singleton x)⁻¹ = fractional_ideal.span_singleton (x⁻¹) :=
fractional_ideal.one_div_span_singleton x

lemma mul_generator_self_inv (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  I * fractional_ideal.span_singleton (generator (I : submodule R₁ g.codomain))⁻¹ = 1 :=
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

lemma invertible_of_principal (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
(fractional_ideal.mul_div_self_cancel_iff).mpr
  ⟨fractional_ideal.span_singleton (generator (I : submodule R₁ g.codomain))⁻¹,
    @mul_generator_self_inv _ _ _ _ _ I _ h⟩

lemma invertible_iff_generator_nonzero (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] :
  I * I⁻¹ = 1 ↔ generator (I : submodule R₁ g.codomain) ≠ 0 :=
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
    have := fractional_ideal.mem_span_singleton_self (generator (I : submodule R₁ g.codomain)),
    rw [hI, fractional_ideal.mem_zero_iff] at this,
    contradiction }
end

lemma is_principal_inv (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  submodule.is_principal (I⁻¹).1 :=
begin
  rw [fractional_ideal.val_eq_coe, fractional_ideal.is_principal_iff],
  use (generator (I : submodule R₁ g.codomain))⁻¹,
  have hI : I  * fractional_ideal.span_singleton ((generator (I : submodule R₁ g.codomain))⁻¹)  = 1,
  apply @mul_generator_self_inv _ _ _ _ _ I _ h,
  apply (@right_inverse_eq _ _ _ _ _ I (fractional_ideal.span_singleton
    ( (generator (I : submodule R₁ g.codomain))⁻¹)) hI).symm,
end

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal
has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_inv : Prop :=
(not_is_field : ¬ is_field A)
(mul_inv_cancel : ∀ I ≠ (⊥ : fractional_ideal (fraction_ring.of A)), I * (1 / I) = 1)

open ring.fractional_ideal

lemma is_dedekind_domain_inv_iff (f : fraction_map A K) :
  is_dedekind_domain_inv A ↔
    (¬ is_field A) ∧ (∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1) :=
begin
  set h : (fraction_ring.of A).codomain ≃ₐ[A] f.codomain := fraction_ring.alg_equiv_of_quotient f,
  split; rintros ⟨hf, hi⟩; use hf; intros I hI,
  { have := hi (map ↑h.symm I) (map_ne_zero _ hI),
    convert congr_arg (map (h : (fraction_ring.of A).codomain →ₐ[A] f.codomain)) this;
      simp only [map_symm_map, map_one, fractional_ideal.map_mul, fractional_ideal.map_div,
                 inv_eq] },
  { have := hi (map ↑h I) (map_ne_zero _ hI),
    convert congr_arg (map (h.symm : f.codomain →ₐ[A] (fraction_ring.of A).codomain)) this;
      simp only [map_map_symm, map_one, fractional_ideal.map_mul, fractional_ideal.map_div,
                 inv_eq] },
end

end inverse
