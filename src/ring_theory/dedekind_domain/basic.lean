/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.ideal.over
import ring_theory.polynomial.rational_root

/-!
# Dedekind domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the notion of a Dedekind domain (or Dedekind ring),
as a Noetherian integrally closed commutative ring of Krull dimension at most one.

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.

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

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_domain A] [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.is_integral_closure (B : Type*) [comm_ring B] [is_domain B]
  [nontrivial R] [algebra R A] [algebra R B] [algebra B A] [is_scalar_tower R B A]
  [is_integral_closure B R A] (h : dimension_le_one R) :
  dimension_le_one B :=
λ p ne_bot prime, by exactI
  is_integral_closure.is_maximal_of_is_maximal_comap A p
    (h _ (is_integral_closure.comap_ne_bot A ne_bot) infer_instance)

lemma dimension_le_one.integral_closure [nontrivial R] [is_domain A] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
h.is_integral_closure R A (integral_closure R A)

variables {R}

lemma dimension_le_one.not_lt_lt (h : ring.dimension_le_one R)
  (p₀ p₁ p₂ : ideal R) [hp₁ : p₁.is_prime] [hp₂ : p₂.is_prime] :
  ¬ (p₀ < p₁ ∧ p₁ < p₂)
| ⟨h01, h12⟩ := h12.ne ((h p₁ (bot_le.trans_lt h01).ne' hp₁).eq_of_le hp₂.ne_top h12.le)

lemma dimension_le_one.eq_bot_of_lt (h : ring.dimension_le_one R)
  (p P : ideal R) [hp : p.is_prime] [hP : P.is_prime] (hpP : p < P) : p = ⊥ :=
by_contra (λ hp0, h.not_lt_lt ⊥ p P ⟨ne.bot_lt hp0, hpP⟩)

end ring

variables [is_domain A]

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
(is_integrally_closed : is_integrally_closed A)

-- See library note [lower instance priority]
attribute [instance, priority 100]
  is_dedekind_domain.is_noetherian_ring is_dedekind_domain.is_integrally_closed

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (K : Type*) [field K] [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain A ↔ is_noetherian_ring A ∧ dimension_le_one A ∧
    (∀ {x : K}, is_integral A x → ∃ y, algebra_map A K y = x) :=
⟨λ ⟨hr, hd, hi⟩, ⟨hr, hd, λ x, (is_integrally_closed_iff K).mp hi⟩,
 λ ⟨hr, hd, hi⟩, ⟨hr, hd, (is_integrally_closed_iff K).mpr @hi⟩⟩

@[priority 100] -- See library note [lower instance priority]
instance is_principal_ideal_ring.is_dedekind_domain [is_principal_ideal_ring A] :
  is_dedekind_domain A :=
⟨principal_ideal_ring.is_noetherian_ring,
 ring.dimension_le_one.principal_ideal_ring A,
 unique_factorization_monoid.is_integrally_closed⟩
