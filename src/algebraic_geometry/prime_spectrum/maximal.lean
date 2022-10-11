/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.prime_spectrum.basic

/-!
# Maximal spectrum of a commutative ring

The maximal spectrum of a commutative ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `maximal_spectrum R`: The maximal spectrum of a commutative ring `R`,
  i.e., the set of all maximal ideals of `R`.

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/

noncomputable theory
open_locale classical

universes u v

variables (R : Type u) [comm_ring R]

/-- The maximal spectrum of a commutative ring `R` is the type of all maximal ideals of `R`. -/
@[nolint has_nonempty_instance] def maximal_spectrum := {I : ideal R // I.is_maximal}

variable {R}

namespace maximal_spectrum

/-- View a point in the maximal spectrum of a commutative ring as an ideal of that ring. -/
abbreviation as_ideal (x : maximal_spectrum R) : ideal R := x.val

@[ext] lemma ext {x y : maximal_spectrum R} : x = y ↔ x.as_ideal = y.as_ideal := subtype.ext_iff_val

instance is_maximal (x : maximal_spectrum R) : x.as_ideal.is_maximal := x.property

instance is_prime (x : maximal_spectrum R) : x.as_ideal.is_prime := x.is_maximal.is_prime

end maximal_spectrum

namespace prime_spectrum

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def of_maximal_spectrum (x : maximal_spectrum R) : prime_spectrum R := ⟨x.val, x.is_prime⟩

lemma of_maximal_spectrum_injective : (@of_maximal_spectrum R _).injective :=
λ ⟨_, _⟩ ⟨_, _⟩, subtype.mk_eq_mk.mpr ∘ subtype.mk.inj

lemma of_maximal_spectrum_range :
  set.range (@of_maximal_spectrum R _) = {x | is_closed ({x} : set $ prime_spectrum R)} :=
begin
  simp only [is_closed_singleton_iff_is_maximal],
  ext ⟨x, _⟩,
  exact ⟨λ ⟨y, hy⟩, hy ▸ y.property, λ hx, ⟨⟨x, hx⟩, rfl⟩⟩
end

end prime_spectrum

namespace maximal_spectrum

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
instance zariski_topology : topological_space $ maximal_spectrum R :=
prime_spectrum.zariski_topology.induced prime_spectrum.of_maximal_spectrum

lemma of_maximal_spectrum_continuous : continuous $ @prime_spectrum.of_maximal_spectrum R _ :=
continuous_induced_dom

end maximal_spectrum
