/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.localization.localization_localization
import tactic.field_simp

/-!

# Localizations of domains as subalgebras of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/

namespace localization
open_locale non_zero_divisors
variables {A : Type*} (K : Type*) [comm_ring A] (S : submonoid A) (hS : S ≤ A⁰)

section comm_ring
variables [comm_ring K] [algebra A K] [is_fraction_ring A K]

/--
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.
-/
def subalgebra (hS : S ≤ A⁰) : subalgebra A K :=
{ algebra_map_mem' := λ a, ⟨algebra_map A _ a, is_localization.lift_eq _ _⟩
  .. (is_localization.lift
  (λ s, by apply is_localization.map_units K ⟨s.1, hS s.2⟩) : localization S →+* K).range }

namespace subalgebra

lemma mem_iff (x : K) :
  x ∈ subalgebra K S hS ↔ ∃ (a : A) (s : S), x = is_localization.mk' K a ⟨s, hS s.2⟩ :=
⟨ by { rintro ⟨x,rfl⟩, obtain ⟨a,s,rfl⟩ := is_localization.mk'_surjective S x,
    use [a, s], apply is_localization.lift_mk' },
  by { rintro ⟨a,s,rfl⟩, use is_localization.mk' _ a s, apply is_localization.lift_mk' } ⟩

instance is_localization_subalgebra :
  is_localization S (subalgebra K S hS) :=
is_localization.is_localization_of_alg_equiv S
{ commutes' := λ x, by { ext, apply is_localization.lift_eq } .. ring_equiv.of_bijective _
  ⟨ begin
      refine λ a b h, (is_localization.lift_injective_iff _).2 (λ a b, _) (subtype.ext_iff.1 h),
      exact ⟨ λ h, congr_arg _ (is_localization.injective _ hS h),
              λ h, congr_arg _ (is_fraction_ring.injective A K h) ⟩,
    end, ring_hom.range_restrict_surjective _ ⟩ }

instance is_fraction_ring : is_fraction_ring (subalgebra K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subalgebra
end comm_ring

section field
variables [field K] [algebra A K] [is_fraction_ring A K]
namespace subalgebra

lemma mem_iff_of_field (x : K) :
  x ∈ subalgebra K S hS ↔ ∃ (a s : A) (hs : s ∈ S), x = algebra_map A K a * (algebra_map A K s)⁻¹ :=
begin
  rw mem_iff, unfold is_localization.mk' submonoid.localization_map.mk',
  simp_rw units.coe_inv', split,
  { rintro ⟨a,s,rfl⟩, use [a,s,s.2], rw is_unit.coe_lift_right, refl },
  { rintro ⟨a,s,hs,rfl⟩, use [a,s,hs], rw is_unit.coe_lift_right, refl },
end

end subalgebra
end field

end localization
