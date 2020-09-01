/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.discrete_valuation_ring
import order.zorn

namespace ring

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def dimension_le_one (R : Type*) [comm_ring R] : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

end ring

open ideal ring

lemma is_principal_ideal_ring.dimension_le_one (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.dimension_le_one R :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

lemma integral_closure.dimension_le_one [comm_ring R] [nontrivial R] [integral_domain K] [algebra R K]
  (h : dimension_le_one R) :
  dimension_le_one (integral_closure R K) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

/-- A Dedekind domain is a nonfield that is Noetherian, integrally closed, and has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).
This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
(not_is_field : ¬ is_field R)
(is_noetherian_ring : is_noetherian_ring R)
(dimension_le_one : dimension_le_one R)
(is_integrally_closed : integral_closure R f.codomain = ⊥)

/-- A Dedekind domain is a nonfield that is Noetherian, and the localization at every nonzero prime is a discrete valuation ring.
This is equivalent to `is_dedekind_domain`.
-/
structure is_dedekind_domain_dvr [integral_domain R]: Prop :=
(not_is_field : ¬ is_field R)
(is_noetherian_ring : is_noetherian_ring R)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal R), P.is_prime →
  @discrete_valuation_ring (localization.at_prime P) (by {exact localization_map.integral_domain_of_local_at_prime a}))

/-- A dedekind domain is a nonfield such that every fractional ideal has an inverse.
This is equivalent to `is_dedekind_domain`
-/
structure is_dedekind_domain_inv [integral_domain R] [comm_ring K] (f : fraction_map R K) : Prop :=
(not_is_field : ¬ is_field R)
(is_invertible_ideal : ∀ I : ring.fractional_ideal f, ⊥ < I → (∃ J : ring.fractional_ideal f, I * J = 1))
