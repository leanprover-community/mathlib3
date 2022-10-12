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
@[ext] structure maximal_spectrum :=
(as_ideal : ideal R)
(is_maximal : as_ideal.is_maximal)

attribute [instance] maximal_spectrum.is_maximal

variable {R}

namespace maximal_spectrum

instance [nontrivial R] : nonempty $ maximal_spectrum R :=
⟨⟨(ideal.exists_maximal R).some, (ideal.exists_maximal R).some_spec⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def to_prime_spectrum (x : maximal_spectrum R) : prime_spectrum R :=
⟨x.as_ideal, x.is_maximal.is_prime⟩

lemma to_prime_spectrum_injective : (@to_prime_spectrum R _).injective :=
λ ⟨_, _⟩ ⟨_, _⟩ h, by simpa only [maximal_spectrum.mk.inj_eq] using subtype.mk.inj h

open prime_spectrum set

lemma to_prime_spectrum_range :
  set.range (@to_prime_spectrum R _) = {x | is_closed ({x} : set $ prime_spectrum R)} :=
begin
  simp only [is_closed_singleton_iff_is_maximal],
  ext ⟨x, _⟩,
  exact ⟨λ ⟨y, hy⟩, hy ▸ y.is_maximal, λ hx, ⟨⟨x, hx⟩, rfl⟩⟩
end

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
instance zariski_topology : topological_space $ maximal_spectrum R :=
prime_spectrum.zariski_topology.induced to_prime_spectrum

instance : t1_space $ maximal_spectrum R :=
⟨λ x, is_closed_induced_iff.mpr
  ⟨{to_prime_spectrum x}, (is_closed_singleton_iff_is_maximal _).mpr x.is_maximal,
    by simpa only [← image_singleton] using preimage_image_eq {x} to_prime_spectrum_injective⟩⟩

lemma to_prime_spectrum_continuous : continuous $ @to_prime_spectrum R _ := continuous_induced_dom

end maximal_spectrum
