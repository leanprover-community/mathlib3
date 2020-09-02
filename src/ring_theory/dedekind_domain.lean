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

TODO

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

lemma is_principal_ideal_ring.dimension_le_one
  [is_principal_ideal_ring A] : ring.dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma integral_closure.dimension_le_one [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

/--
A Dedekind domain is a nonfield that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
-- TODO: R should be a `comm_ring`
class is_dedekind_domain (R : Type*) [integral_domain R] : Prop :=
(not_is_field : ¬ is_field R)
(is_noetherian_ring : is_noetherian_ring R)
(dimension_le_one : dimension_le_one R)
(is_integrally_closed : integral_closure R (fraction_ring R) = ⊥)

/-- The non-field, noetherian ring, dimension ≤ 1, integrally closed definition of Dedekind domain
doesn't depend on the choice of fraction field. -/
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
A Dedekind domain is a nonfield that is Noetherian, and the localization at
every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

/--
A Dedekind domain is a nonfield such that every fractional ideal has an inverse.

TODO:
The fractional ideals are independent of the choice of field of fractions:
use `is_dedekind_domain_inv_iff` to prove `is_dedekind_domain_inv` for a given `fraction_map`.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
-- TODO: choose that `f` is the fraction_map from `A` to `fraction_ring A` and show the independence of `f`
structure is_dedekind_domain_inv (f : fraction_map A K) : Prop :=
(not_is_field : ¬ is_field R)
(mul_inv_cancel : ∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1)
