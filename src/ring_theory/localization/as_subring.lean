/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.localization.localization_localization
import tactic.field_simp

/-!

# Localizations of domains as subrings of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subring of the field `K`.

-/

namespace localization

variables
  {A : Type*} (K : Type*) [comm_ring A] [comm_ring K]
  [algebra A K] [is_fraction_ring A K]

open_locale non_zero_divisors

variables (S : submonoid A) (hS : S ≤ A⁰)
include hS

/--
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subring of `K`.
-/
noncomputable def subring : subring K :=
(is_localization.lift
  (λ s, by apply is_localization.map_units K ⟨s.1, hS s.2⟩) : localization S →+* K).range

namespace subring

lemma mem_iff (x : K) :
  x ∈ subring K S hS ↔ ∃ (a : A) (s : S), x * algebra_map A K s = algebra_map A K a :=
begin
  split,
  { rintro ⟨y,rfl⟩, obtain ⟨w,h⟩ := is_localization.surj S y, use [w.1, w.2],
    convert ← congr_arg (is_localization.lift _) h using 1,
    { rw map_mul, congr, apply is_localization.lift_eq }, apply is_localization.lift_eq },
  { rintro ⟨a,s,h⟩, use is_localization.mk' _ a s,
    rw [is_localization.lift_mk'_spec, mul_comm, h] },
end

noncomputable instance algebra : algebra A (subring K S hS) :=
ring_hom.to_algebra $ (ring_hom.range_restrict _).comp $ algebra_map A (localization S)

@[simp] lemma coe_algebra_hom_apply (a : A) :
  (algebra_map A (subring K S hS) a : K) = algebra_map A K a :=
is_localization.lift_eq _ a

instance scalar_tower : is_scalar_tower A (subring K S hS) K :=
is_scalar_tower.of_algebra_map_eq $ λ a, (coe_algebra_hom_apply K S hS a).symm

instance is_localization_subring :
  is_localization S (subring K S hS) :=
is_localization.is_localization_of_alg_equiv S
{ commutes' := λ _, rfl .. ring_equiv.of_bijective _
  ⟨ begin
      refine λ a b h, (is_localization.lift_injective_iff _).2 (λ a b, _) (subtype.ext_iff.1 h),
      exact ⟨ λ h, congr_arg _ (is_localization.injective _ hS h),
              λ h, congr_arg _ (is_fraction_ring.injective A K h) ⟩,
    end, ring_hom.range_restrict_surjective _ ⟩ }

instance is_fraction_ring : is_fraction_ring (subring K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subring
end localization
