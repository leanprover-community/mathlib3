/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import ring_theory.localization
import ring_theory.int.basic

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial is irreducible iff it is irreducible in a fraction field.
 - `is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.

-/

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

section
variables {S : Type*} [integral_domain S] {φ : R →+* S} (hinj : function.injective φ)
variables {f : polynomial R} (hf : f.is_primitive)
include hinj hf

lemma is_primitive.is_unit_iff_is_unit_map_of_injective :
  is_unit f ↔ is_unit (map φ f) :=
begin
  refine ⟨(ring_hom.of (map φ)).is_unit_map, λ h, _⟩,
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  have hdeg := degree_C u.ne_zero,
  rw [hu, degree_map' hinj] at hdeg,
  rw [eq_C_of_degree_eq_zero hdeg, is_primitive, content_C, normalize_eq_one] at hf,
  rwa [eq_C_of_degree_eq_zero hdeg, is_unit_C],
end

lemma is_primitive.irreducible_of_irreducible_map_of_injective (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  refine ⟨λ h, h_irr.1 (is_unit.map (monoid_hom.of (map φ)) h), _⟩,
  intros a b h,
  rcases h_irr.2 (map φ a) (map φ b) (by rw [h, map_mul]) with hu | hu,
  { left,
    rwa (hf.is_primitive_of_dvd (dvd.intro _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj },
  right,
  rwa (hf.is_primitive_of_dvd (dvd.intro_left _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj
end

end

section fraction_map
variables {K : Type*} [field K] (f : fraction_map R K)

lemma is_primitive.is_unit_iff_is_unit_map {p : polynomial R} (hp : p.is_primitive) :
  is_unit p ↔ is_unit (p.map f.to_map) :=
hp.is_unit_iff_is_unit_map_of_injective f.injective

open localization_map

lemma is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part
  {p : polynomial K} (h0 : p ≠ 0) (h : is_unit (f.integer_normalization p).prim_part) :
  is_unit p :=
begin
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := @integer_normalization_map_to_map _ _ _ _ _ f p,
  rw [algebra.smul_def, ← C_eq_algebra_map, subtype.coe_mk] at hc,
  apply is_unit_of_mul_is_unit_right,
  rw [← hc, (f.integer_normalization p).eq_C_content_mul_prim_part, ← hu,
    ← ring_hom.map_mul, is_unit_iff],
  refine ⟨f.to_map ((f.integer_normalization p).content * ↑u),
    is_unit_iff_ne_zero.2 (λ con, _), by simp⟩,
  replace con := (ring_hom.injective_iff f.to_map).1 f.injective _ con,
  rw [mul_eq_zero, content_eq_zero_iff, fraction_map.integer_normalization_eq_zero_iff] at con,
  rcases con with con | con,
  { apply h0 con },
  { apply units.ne_zero _ con },
end

/-- Gauss's Lemma states that a primitive polynomial is irreducible iff it is irreducible in the
  fraction field. -/
theorem is_primitive.irreducible_iff_irreducible_map_fraction_map
  {p : polynomial R} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map f.to_map) :=
begin
  refine ⟨λ hi, ⟨λ h, hi.1 ((hp.is_unit_iff_is_unit_map f).2 h), λ a b hab, _⟩,
    hp.irreducible_of_irreducible_map_of_injective f.injective⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := @integer_normalization_map_to_map _ _ _ _ _ f a,
  obtain ⟨⟨d, d0⟩, hd⟩ := @integer_normalization_map_to_map _ _ _ _ _ f b,
  rw [algebra.smul_def, ← C_eq_algebra_map, subtype.coe_mk] at hc hd,
  rw [submonoid.mem_carrier, mem_non_zero_divisors_iff_ne_zero] at c0 d0,
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0,
  rw [ne.def, ← C_eq_zero] at hcd0,
  have h1 : C c * C d * p = f.integer_normalization a * f.integer_normalization b,
  { apply (map_injective _ f.injective _),
    rw [map_mul, map_mul, map_mul, hc, hd, map_C, map_C, hab],
    ring },
  obtain ⟨u, hu⟩ : associated (c * d) (content (f.integer_normalization a) *
            content (f.integer_normalization b)),
  { rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul,
        normalize.map_mul, normalize_content, normalize_content,
        ← mul_one (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C,
        ← content_mul, ← content_mul, ← content_mul, h1] },
  rw [← ring_hom.map_mul, eq_comm,
    (f.integer_normalization a).eq_C_content_mul_prim_part,
    (f.integer_normalization b).eq_C_content_mul_prim_part, mul_assoc,
    mul_comm _ (C _ * _), ← mul_assoc, ← mul_assoc, ← ring_hom.map_mul, ← hu, ring_hom.map_mul,
    mul_assoc, mul_assoc, ← mul_assoc (C ↑u)] at h1,
  have h0 : (a ≠ 0) ∧ (b ≠ 0),
  { classical,
    rw [ne.def, ne.def, ← decidable.not_or_iff_and_not, ← mul_eq_zero, ← hab],
    intro con,
    apply hp.ne_zero (map_injective _ f.injective _),
    simp [con] },
  rcases hi.2 _ _ (mul_left_cancel' hcd0 h1).symm with h | h,
  { right,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part f h0.2
      (is_unit_of_mul_is_unit_right h) },
  { left,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part f h0.1 h },
end
end fraction_map

/-- Gauss's Lemma for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem is_primitive.int.irreducible_iff_irreducible_map_cast
  {p : polynomial ℤ} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map (int.cast_ring_hom ℚ)) :=
hp.irreducible_iff_irreducible_map_fraction_map fraction_map.int.fraction_map

end gcd_monoid
end polynomial
