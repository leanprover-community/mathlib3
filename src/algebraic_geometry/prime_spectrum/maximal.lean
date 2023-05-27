/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.prime_spectrum.basic
import ring_theory.localization.as_subring

/-!
# Maximal spectrum of a commutative ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
let ⟨I, hI⟩ := ideal.exists_maximal R in ⟨⟨I, hI⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def to_prime_spectrum (x : maximal_spectrum R) : prime_spectrum R :=
⟨x.as_ideal, x.is_maximal.is_prime⟩

lemma to_prime_spectrum_injective : (@to_prime_spectrum R _).injective :=
λ ⟨_, _⟩ ⟨_, _⟩ h, by simpa only [mk.inj_eq] using (prime_spectrum.ext_iff _ _).mp h

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

variables (R) [is_domain R] (K : Type v) [field K] [algebra R K] [is_fraction_ring R K]

/-- An integral domain is equal to the intersection of its localizations at all its maximal ideals
viewed as subalgebras of its field of fractions. -/
theorem infi_localization_eq_bot :
  (⨅ v : maximal_spectrum R,
    localization.subalgebra.of_field K _ v.as_ideal.prime_compl_le_non_zero_divisors) = ⊥ :=
begin
  ext x,
  rw [algebra.mem_bot, algebra.mem_infi],
  split,
  { apply imp_of_not_imp_not,
    intros hrange hlocal,
    let denom : ideal R := (submodule.span R {1} : submodule R K).colon (submodule.span R {x}),
    have hdenom : (1 : R) ∉ denom :=
    begin
      intro hdenom,
      rcases submodule.mem_span_singleton.mp
        (submodule.mem_colon.mp hdenom x $ submodule.mem_span_singleton_self x) with ⟨y, hy⟩,
      exact hrange ⟨y, by rw [← mul_one $ algebra_map R K y, ← algebra.smul_def, hy, one_smul]⟩
    end,
    rcases denom.exists_le_maximal (λ h, (h ▸ hdenom) submodule.mem_top) with ⟨max, hmax, hle⟩,
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩,
    apply hd (hle $ submodule.mem_colon.mpr $ λ _ hy, _),
    rcases submodule.mem_span_singleton.mp hy with ⟨y, rfl⟩,
    exact submodule.mem_span_singleton.mpr
      ⟨y * n, by rw [algebra.smul_def, mul_one, map_mul, smul_comm, algebra.smul_def,
                     algebra.smul_def, mul_comm $ algebra_map R K d, inv_mul_cancel_right₀ $
                       (map_ne_zero_iff _ $ no_zero_smul_divisors.algebra_map_injective R K).mpr $
                       λ h, (h ▸ hd) max.zero_mem]⟩ },
  { rintro ⟨y, rfl⟩ ⟨v, hv⟩,
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩ }
end

end maximal_spectrum

namespace prime_spectrum

variables (R) [is_domain R] (K : Type v) [field K] [algebra R K] [is_fraction_ring R K]

/-- An integral domain is equal to the intersection of its localizations at all its prime ideals
viewed as subalgebras of its field of fractions. -/
theorem infi_localization_eq_bot :
  (⨅ v : prime_spectrum R,
    localization.subalgebra.of_field K _ $ v.as_ideal.prime_compl_le_non_zero_divisors) = ⊥ :=
begin
  ext x,
  rw [algebra.mem_infi],
  split,
  { rw [← maximal_spectrum.infi_localization_eq_bot, algebra.mem_infi],
    exact λ hx ⟨v, hv⟩, hx ⟨v, hv.is_prime⟩ },
  { rw [algebra.mem_bot],
    rintro ⟨y, rfl⟩ ⟨v, hv⟩,
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩ }
end

end prime_spectrum
