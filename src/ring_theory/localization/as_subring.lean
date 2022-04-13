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
  {A : Type*} (K : Type*) [comm_ring A] [is_domain A] [field K]
  [algebra A K] [is_fraction_ring A K]

open_locale non_zero_divisors

lemma algebra_map_apply_ne_zero_of_le
  {S : submonoid A} (hS : S ≤ A⁰) (s : A) (hs : s ∈ S) : algebra_map A K s ≠ 0 :=
begin
  intros c, rw ← (algebra_map A K).map_zero at c,
  replace hs := hS hs, rw mem_non_zero_divisors_iff_ne_zero at hs,
  replace c := is_fraction_ring.injective _ _ c,
  exact hs c,
end

/--
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subring of `K`.
-/
def subring (S : submonoid A) (hS : S ≤ A⁰) : subring K :=
{ carrier := { x | ∃ (a s : A) (hs : s ∈ S),
    x = algebra_map A K a * (algebra_map A K s)⁻¹ },
  mul_mem' := begin
    rintros _ _ ⟨a, s, hs, rfl⟩ ⟨b, t, ht, rfl⟩,
    refine ⟨a * b, s * t, S.mul_mem hs ht, _⟩,
    simp only [ring_hom.map_mul],
    field_simp,
  end,
  one_mem' := ⟨1, 1, S.one_mem, by simp⟩,
  add_mem' := begin
    rintros _ _ ⟨a, s, hs, rfl⟩ ⟨b, t, ht, rfl⟩,
    refine ⟨a * t + b * s, s * t, S.mul_mem hs ht, _⟩,
    simp only [ring_hom.map_mul, ring_hom.map_add],
    have : algebra_map A K s ≠ 0 := algebra_map_apply_ne_zero_of_le K hS s hs,
    have : algebra_map A K t ≠ 0 := algebra_map_apply_ne_zero_of_le K hS t ht,
    field_simp,
  end,
  zero_mem' := ⟨0, 1, S.one_mem, by simp⟩,
  neg_mem' := begin
    rintros _ ⟨a, s, hs, rfl⟩,
    refine ⟨-a, s, hs, by simp⟩,
  end } .

namespace subring

variables (S : submonoid A) (hS : S ≤ A⁰)

instance algebra : algebra A (subring K S hS) :=
{ smul := λ a x, ⟨a • x, begin
    obtain ⟨b,s,hs,hx⟩ := x.2, dsimp at hx, rw hx,
    refine ⟨a * b, s, hs, _⟩,
    simp [algebra.smul_def, mul_assoc],
  end⟩,
  to_fun := λ a, ⟨algebra_map A K a, a, 1, S.one_mem, by simp⟩,
  map_one' := subtype.ext $ (algebra_map A K).map_one,
  map_mul' := λ a b, subtype.ext $ (algebra_map A K).map_mul a b,
  map_zero' := subtype.ext $ (algebra_map A K).map_zero,
  map_add' := λ a b, subtype.ext $ (algebra_map A K).map_add a b,
  commutes' := λ a x, mul_comm _ _,
  smul_def' := λ a x, subtype.ext $ algebra.smul_def _ _ }

@[simp] lemma coe_algebra_hom_apply (a : A) :
  (algebra_map A (subring K S hS) a : K) = algebra_map A K a := rfl

instance scalar_tower : is_scalar_tower A (subring K S hS) K :=
{ smul_assoc := begin
    intros x y z,
    simpa only [algebra.smul_def, mul_assoc, map_mul],
  end }

instance is_localization_subring :
  is_localization S (subring K S hS) :=
{ map_units := begin
    rintros ⟨s,hs⟩,
    have : algebra_map A K s ≠ 0 := algebra_map_apply_ne_zero_of_le K hS s hs,
    refine ⟨⟨_,⟨_,1,s,hs,rfl⟩, _,_⟩,rfl⟩,
    { ext, dsimp, field_simp },
    { ext, dsimp, field_simp },
  end,
  surj := begin
    rintros ⟨z,a,s,hs,rfl⟩,
    refine ⟨⟨a,⟨s,hs⟩⟩, _⟩,
    have : algebra_map A K s ≠ 0 := algebra_map_apply_ne_zero_of_le K hS s hs,
    ext, dsimp, field_simp,
  end,
  eq_iff_exists := begin
    intros a b, split,
    { intros h, use 1,
      apply_fun (algebra_map _ K) at h,
      simp only [← is_scalar_tower.algebra_map_apply] at h,
      push_cast, simp only [mul_one],
      exact is_fraction_ring.injective _ _ h },
    { rintros ⟨⟨s,hs⟩,h⟩,
      ext, dsimp, apply_fun (algebra_map _ K) at h,
      simp only [ring_hom.map_mul] at h,
      have : algebra_map A K s ≠ 0 := algebra_map_apply_ne_zero_of_le K hS s hs,
      simp only [set_like.coe_mk, mul_eq_mul_right_iff] at h, cases h,
      { assumption }, { contradiction } }
  end }

instance is_fraction_ring : is_fraction_ring (subring K S hS) K :=
is_fraction_ring.is_fraction_ring_of_is_localization S _ _ hS

end subring
end localization
