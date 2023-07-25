/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
import ring_theory.localization.localization_localization

/-!

# Localizations of domains as subalgebras of the fraction field.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/

namespace localization
open_locale non_zero_divisors
variables {A : Type*} (K : Type*) [comm_ring A] (S : submonoid A) (hS : S ≤ A⁰)

section comm_ring
variables [comm_ring K] [algebra A K] [is_fraction_ring A K]

lemma map_is_unit_of_le (hS : S ≤ A⁰) (s : S) : is_unit (algebra_map A K s) :=
by apply is_localization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

/-- The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`. -/
noncomputable
def map_to_fraction_ring (B : Type*) [comm_ring B] [algebra A B]
  [is_localization S B] (hS : S ≤ A⁰) :
  B →ₐ[A] K :=
{ commutes' := λ a, by simp,
  ..is_localization.lift (map_is_unit_of_le K S hS) }

@[simp]
lemma map_to_fraction_ring_apply {B : Type*} [comm_ring B] [algebra A B]
  [is_localization S B] (hS : S ≤ A⁰) (b : B) :
  map_to_fraction_ring K S B hS b = is_localization.lift (map_is_unit_of_le K S hS) b := rfl

lemma mem_range_map_to_fraction_ring_iff (B : Type*) [comm_ring B] [algebra A B]
  [is_localization S B] (hS : S ≤ A⁰) (x : K) :
  x ∈ (map_to_fraction_ring K S B hS).range ↔
  ∃ (a s : A) (hs : s ∈ S), x = is_localization.mk' K a ⟨s, hS hs⟩ :=
⟨ by { rintro ⟨x,rfl⟩, obtain ⟨a,s,rfl⟩ := is_localization.mk'_surjective S x,
    use [a, s, s.2], apply is_localization.lift_mk' },
  by { rintro ⟨a,s,hs,rfl⟩, use is_localization.mk' _ a ⟨s,hs⟩,
    apply is_localization.lift_mk' } ⟩

instance is_localization_range_map_to_fraction_ring (B : Type*) [comm_ring B] [algebra A B]
  [is_localization S B] (hS : S ≤ A⁰) :
  is_localization S (map_to_fraction_ring K S B hS).range :=
is_localization.is_localization_of_alg_equiv S $ show B ≃ₐ[A] _, from alg_equiv.of_bijective
(map_to_fraction_ring K S B hS).range_restrict
begin
  refine ⟨λ a b h, _, set.surjective_onto_range⟩,
  refine (is_localization.lift_injective_iff _).2 (λ a b, _) (subtype.ext_iff.1 h),
  exact ⟨λ h, congr_arg _ (is_localization.injective _ hS h),
         λ h, congr_arg _ (is_fraction_ring.injective A K h)⟩,
end

instance is_fraction_ring_range_map_to_fraction_ring
  (B : Type*) [comm_ring B] [algebra A B]
  [is_localization S B] (hS : S ≤ A⁰) :
  is_fraction_ring (map_to_fraction_ring K S B hS).range K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

/--
Given a commutative ring `A` with fraction ring `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`is_localization.mk' K a ⟨s, _⟩`, where `s ∈ S`.
-/
noncomputable
def subalgebra (hS : S ≤ A⁰) : subalgebra A K :=
(map_to_fraction_ring K S (localization S) hS).range.copy
{ x | ∃ (a s : A) (hs : s ∈ S), x = is_localization.mk' K a ⟨s, hS hs⟩ } $
by { ext, symmetry, apply mem_range_map_to_fraction_ring_iff }

namespace subalgebra

instance is_localization_subalgebra :
  is_localization S (subalgebra K S hS) :=
by { dunfold localization.subalgebra, rw subalgebra.copy_eq, apply_instance }

instance is_fraction_ring : is_fraction_ring (subalgebra K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subalgebra
end comm_ring

section field
variables [field K] [algebra A K] [is_fraction_ring A K]
namespace subalgebra

lemma mem_range_map_to_fraction_ring_iff_of_field
  (B : Type*) [comm_ring B] [algebra A B] [is_localization S B] (x : K) :
  x ∈ (map_to_fraction_ring K S B hS).range ↔
  ∃ (a s : A) (hs : s ∈ S), x = algebra_map A K a * (algebra_map A K s)⁻¹ :=
begin
  rw mem_range_map_to_fraction_ring_iff,
  iterate 3 { congr' with }, convert iff.rfl, rw units.coe_inv, refl,
end

/--
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`algebra_map A K a * (algebra_map A K s)⁻¹` where `a s : A` and `s ∈ S`.
-/
noncomputable
def of_field : _root_.subalgebra A K :=
(map_to_fraction_ring K S (localization S) hS).range.copy
{ x | ∃ (a s : A) (hs : s ∈ S), x = algebra_map A K a * (algebra_map A K s)⁻¹ } $
by { ext, symmetry, apply mem_range_map_to_fraction_ring_iff_of_field }

instance is_localization_of_field :
  is_localization S (subalgebra.of_field K S hS) :=
by { dunfold localization.subalgebra.of_field, rw subalgebra.copy_eq, apply_instance }

instance is_fraction_ring_of_field : is_fraction_ring (subalgebra.of_field K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subalgebra
end field

end localization
