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
open_locale non_zero_divisors
variables {A : Type*} (K : Type*) [comm_ring A] (S : submonoid A) (hS : S ≤ A⁰)

section comm_ring
variables [comm_ring K] [algebra A K] [is_fraction_ring A K]

/--
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subring of `K`.
-/
noncomputable def subring (hS : S ≤ A⁰) : subring K :=
(is_localization.lift
  (λ s, by apply is_localization.map_units K ⟨s.1, hS s.2⟩) : localization S →+* K).range

namespace subring

lemma mem_iff (x : K) :
  x ∈ subring K S hS ↔ ∃ (a : A) (s : S), x * algebra_map A K s = algebra_map A K a :=
⟨ begin
    rintro ⟨y,rfl⟩, obtain ⟨w,h⟩ := is_localization.surj S y, use [w.1, w.2],
    convert ← congr_arg (is_localization.lift _) h using 1,
    { rw map_mul, congr, apply is_localization.lift_eq }, apply is_localization.lift_eq,
  end,
  λ ⟨a,s,h⟩, ⟨ is_localization.mk' _ a s, by rw [is_localization.lift_mk'_spec, mul_comm, h] ⟩ ⟩

noncomputable instance algebra : algebra A (subring K S hS) :=
((algebra_map A K).cod_restrict' (subring K S hS) $
  λ x, ⟨algebra_map A _ x, is_localization.lift_eq _ _⟩).to_algebra

@[simp] lemma coe_algebra_hom_apply (a : A) :
  (algebra_map A (subring K S hS) a : K) = algebra_map A K a := rfl

instance scalar_tower : is_scalar_tower A (subring K S hS) K :=
is_scalar_tower.of_algebra_map_eq $ λ a, (coe_algebra_hom_apply K S hS a).symm

instance is_localization_subring :
  is_localization S (subring K S hS) :=
is_localization.is_localization_of_alg_equiv S
{ commutes' := λ x, by { ext, apply is_localization.lift_eq } .. ring_equiv.of_bijective _
  ⟨ begin
      refine λ a b h, (is_localization.lift_injective_iff _).2 (λ a b, _) (subtype.ext_iff.1 h),
      exact ⟨ λ h, congr_arg _ (is_localization.injective _ hS h),
              λ h, congr_arg _ (is_fraction_ring.injective A K h) ⟩,
    end, ring_hom.range_restrict_surjective _ ⟩ }

instance is_fraction_ring : is_fraction_ring (subring K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subring
end comm_ring

section field
variables [field K] [algebra A K] [is_fraction_ring A K]
namespace subring

lemma mem_iff_of_field (x : K) :
  x ∈ subring K S hS ↔ ∃ (a s : A) (hs : s ∈ S), x = algebra_map A K a * (algebra_map A K s)⁻¹ :=
begin
  rw mem_iff, haveI := (algebra_map A K).domain_nontrivial,
  split,
  { rintro ⟨a,s,h⟩, use [a, s, s.2], rw eq_mul_inv_iff_mul_eq₀,
    exacts [h, is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors (hS s.2)] },
  { rintro ⟨a,s,hs,he⟩, use [a, ⟨s,hs⟩], rw ← eq_mul_inv_iff_mul_eq₀,
    exacts [he, is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors (hS hs)] },
end

end subring
end field

end localization
