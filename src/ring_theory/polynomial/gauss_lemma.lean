/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.int.basic
import field_theory.splitting_field
import ring_theory.localization.integral
import ring_theory.integrally_closed


/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.monic.irreducible_iff_irreducible_map_fraction_map`:
  A monic polynomial over an integrally closed domain is irreducible iff it is irreducible in a
    fraction field
 - `is_integrally_closed_iff'`:
   Integrally closed domains are precisely the domains for in which Gauss's lemma holds
    for monic polynomials
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial over a GCD domain is irreducible iff it is irreducible in a fraction field
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials over a GCD domain divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/

open_locale non_zero_divisors polynomial

variables {R : Type*} [comm_ring R]

namespace polynomial

section
variables {S : Type*} [comm_ring S] [is_domain S]
variables {φ : R →+* S} (hinj : function.injective φ) {f : R[X]} (hf : f.is_primitive)
include hinj hf

lemma is_primitive.is_unit_iff_is_unit_map_of_injective :
  is_unit f ↔ is_unit (map φ f) :=
begin
  refine ⟨(map_ring_hom φ).is_unit_map, λ h, _⟩,
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  have hdeg := degree_C u.ne_zero,
  rw [hu, degree_map_eq_of_injective hinj] at hdeg,
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢,
  exact is_unit_C.mpr (is_primitive_iff_is_unit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl),
end

lemma is_primitive.irreducible_of_irreducible_map_of_injective (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  refine ⟨λ h, h_irr.not_unit (is_unit.map (map_ring_hom φ) h),
    λ a b h, (h_irr.is_unit_or_is_unit $ by rw [h, polynomial.map_mul]).imp _ _⟩,
  all_goals { apply ((is_primitive_of_dvd hf _).is_unit_iff_is_unit_map_of_injective hinj).mpr },
  exacts [(dvd.intro _ h.symm), dvd.intro_left _ h.symm],
end

end

section fraction_map

variables {K : Type*} [field K] [algebra R K] [is_fraction_ring R K]

lemma is_primitive.is_unit_iff_is_unit_map {p : R[X]} (hp : p.is_primitive) :
  is_unit p ↔ is_unit (p.map (algebra_map R K)) :=
hp.is_unit_iff_is_unit_map_of_injective (is_fraction_ring.injective _ _)

variable [is_domain R]

section is_integrally_closed

open is_integrally_closed

/-- **Gauss's Lemma** for integrally closed domains states that a monic polynomial is irreducible
  iff it is irreducible in the fraction field. -/
theorem monic.irreducible_iff_irreducible_map_fraction_map [is_integrally_closed R] {p : R[X]}
  (h : p.monic) : irreducible p ↔ irreducible (p.map $ algebra_map R K) :=
begin
  /- The ← direction follows from `is_primitive.irreducible_of_irreducible_map_of_injective`.
     For the → direction, it is enought to show that if `(p.map $ algebra_map R K) = a * b` and
     `a` is not a unit then `b` is a unit -/
  refine ⟨λ hp, irreducible_iff.mpr ⟨hp.not_unit.imp h.is_primitive.is_unit_iff_is_unit_map.mpr,
    λ a b H, or_iff_not_imp_left.mpr (λ hₐ, _)⟩,
    λ hp, h.is_primitive.irreducible_of_irreducible_map_of_injective
      (is_fraction_ring.injective R K) hp⟩,

  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm),
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm),

  have : a.leading_coeff * b.leading_coeff = 1,
  { rw [← leading_coeff_mul, ← H, monic.leading_coeff (h.map $ algebra_map R K)] },

  rw [← ha, ← hb, mul_comm _ (C b.leading_coeff), mul_assoc, ← mul_assoc (C a.leading_coeff),
    ← C_mul, this, C_1, one_mul, ← polynomial.map_mul] at H,
  rw [← hb, ← polynomial.coe_map_ring_hom],
  refine is_unit.mul
    (is_unit.map _ (or.resolve_left (hp.is_unit_or_is_unit _) (show ¬ is_unit a', from _)))
    (is_unit_iff_exists_inv'.mpr (exists.intro (C a.leading_coeff) $ by rwa [← C_mul, this, C_1])),
  { exact polynomial.map_injective _ (is_fraction_ring.injective R K) H },

  { by_contra h_contra,
    refine hₐ _,
    rw [← ha, ← polynomial.coe_map_ring_hom],
    exact is_unit.mul (is_unit.map _ h_contra) (is_unit_iff_exists_inv.mpr
      (exists.intro (C b.leading_coeff) $ by rwa [← C_mul, this, C_1])) },
end

/-- Integrally closed domains are precisely the domains for in which Gauss's lemma holds
    for monic polynomials -/
theorem is_integrally_closed_iff' : is_integrally_closed R ↔
  ∀ p : R[X], p.monic → (irreducible p ↔ irreducible (p.map $ algebra_map R K)) :=
begin
  split,
  { intros hR p hp, letI := hR, exact monic.irreducible_iff_irreducible_map_fraction_map hp },
  { intro H,
    refine (is_integrally_closed_iff K).mpr (λ x hx, ring_hom.mem_range.mp $
      minpoly.mem_range_of_degree_eq_one R x _),
    rw ← monic.degree_map (minpoly.monic hx) (algebra_map R K),
    apply degree_eq_one_of_irreducible_of_root ((H _ $ minpoly.monic hx).mp
      (minpoly.irreducible hx)),
    rw [is_root, eval_map, ← aeval_def, minpoly.aeval R x] },
end

theorem monic.dvd_of_fraction_map_dvd_fraction_map [is_integrally_closed R] {p q : R[X]}
  (hp : p.monic ) (hq : q.monic) (h : q.map (algebra_map R K) ∣ p.map (algebra_map R K)) : q ∣ p :=
begin
  obtain ⟨r, hr⟩ := h,
  obtain ⟨d', hr'⟩ := is_integrally_closed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm),
  rw [monic.leading_coeff, C_1, mul_one] at hr',
  rw [← hr', ← polynomial.map_mul] at hr,
  exact dvd_of_mul_right_eq _ (polynomial.map_injective _ (is_fraction_ring.injective R K) hr.symm),
   { exact monic.of_mul_monic_left (hq.map (algebra_map R K)) (by simpa [←hr] using hp.map _) },
end

theorem monic.dvd_iff_fraction_map_dvd_fraction_map [is_integrally_closed R] {p q : R[X]}
  (hp : p.monic ) (hq : q.monic) : q.map (algebra_map R K) ∣ p.map (algebra_map R K) ↔ q ∣ p :=
⟨λ h, hp.dvd_of_fraction_map_dvd_fraction_map hq h,
  λ ⟨a,b⟩, ⟨a.map (algebra_map R K), b.symm ▸ polynomial.map_mul (algebra_map R K)⟩⟩

end is_integrally_closed

open is_localization

section normalized_gcd_monoid

variable [normalized_gcd_monoid R]

lemma is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part
  {p : K[X]} (h0 : p ≠ 0) (h : is_unit (integer_normalization R⁰ p).prim_part) :
  is_unit p :=
begin
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ p,
  rw [subtype.coe_mk, algebra.smul_def, algebra_map_apply] at hc,
  apply is_unit_of_mul_is_unit_right,
  rw [← hc, (integer_normalization R⁰ p).eq_C_content_mul_prim_part, ← hu,
    ← ring_hom.map_mul, is_unit_iff],
  refine ⟨algebra_map R K ((integer_normalization R⁰ p).content * ↑u),
    is_unit_iff_ne_zero.2 (λ con, _), by simp⟩,
  replace con := (injective_iff_map_eq_zero (algebra_map R K)).1
    (is_fraction_ring.injective _ _) _ con,
  rw [mul_eq_zero, content_eq_zero_iff, is_fraction_ring.integer_normalization_eq_zero_iff] at con,
  rcases con with con | con,
  { apply h0 con },
  { apply units.ne_zero _ con },
end

/-- **Gauss's Lemma** for GCD domains states that a primitive polynomial is irreducible iff it is
  irreducible in the fraction field. -/
theorem is_primitive.irreducible_iff_irreducible_map_fraction_map
  {p : R[X]} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map (algebra_map R K)) :=
begin
  refine ⟨λ hi, ⟨λ h, hi.not_unit (hp.is_unit_iff_is_unit_map.2 h), λ a b hab, _⟩,
    hp.irreducible_of_irreducible_map_of_injective (is_fraction_ring.injective _ _)⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ a,
  obtain ⟨⟨d, d0⟩, hd⟩ := integer_normalization_map_to_map R⁰ b,
  rw [algebra.smul_def, algebra_map_apply, subtype.coe_mk] at hc hd,
  rw mem_non_zero_divisors_iff_ne_zero at c0 d0,
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0,
  rw [ne.def, ← C_eq_zero] at hcd0,
  have h1 : C c * C d * p = integer_normalization R⁰ a * integer_normalization R⁰ b,
  { apply map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _,
    rw [polynomial.map_mul, polynomial.map_mul, polynomial.map_mul, hc, hd, map_C, map_C, hab],
    ring },
  obtain ⟨u, hu⟩ : associated (c * d) (content (integer_normalization R⁰ a) *
            content (integer_normalization R⁰ b)),
  { rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul,
        normalize.map_mul, normalize_content, normalize_content,
        ← mul_one (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C,
        ← content_mul, ← content_mul, ← content_mul, h1] },
  rw [← ring_hom.map_mul, eq_comm,
    (integer_normalization R⁰ a).eq_C_content_mul_prim_part,
    (integer_normalization R⁰ b).eq_C_content_mul_prim_part, mul_assoc,
    mul_comm _ (C _ * _), ← mul_assoc, ← mul_assoc, ← ring_hom.map_mul, ← hu, ring_hom.map_mul,
    mul_assoc, mul_assoc, ← mul_assoc (C ↑u)] at h1,
  have h0 : (a ≠ 0) ∧ (b ≠ 0),
  { classical,
    rw [ne.def, ne.def, ← decidable.not_or_iff_and_not, ← mul_eq_zero, ← hab],
    intro con,
    apply hp.ne_zero (map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _),
    simp [con] },
  rcases hi.is_unit_or_is_unit (mul_left_cancel₀ hcd0 h1).symm with h | h,
  { right,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.2
      (is_unit_of_mul_is_unit_right h) },
  { left,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.1 h },
end

lemma is_primitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]}
  (hp : p.is_primitive) (hq : q.is_primitive)
  (h_dvd : p.map (algebra_map R K) ∣ q.map (algebra_map R K)) : p ∣ q :=
begin
  rcases h_dvd with ⟨r, hr⟩,
  obtain ⟨⟨s, s0⟩, hs⟩ := integer_normalization_map_to_map R⁰ r,
  rw [subtype.coe_mk, algebra.smul_def, algebra_map_apply] at hs,
  have h : p ∣ q * C s,
  { use (integer_normalization R⁰ r),
    apply map_injective (algebra_map R K) (is_fraction_ring.injective _ _),
    rw [polynomial.map_mul, polynomial.map_mul, hs, hr, mul_assoc, mul_comm r],
    simp },
  rw [← hp.dvd_prim_part_iff_dvd, prim_part_mul, hq.prim_part_eq,
      associated.dvd_iff_dvd_right] at h,
  { exact h },
  { symmetry,
    rcases is_unit_prim_part_C s with ⟨u, hu⟩,
    use u,
    rw hu },
  iterate 2 { apply mul_ne_zero hq.ne_zero,
    rw [ne.def, C_eq_zero],
    contrapose! s0,
    simp [s0, mem_non_zero_divisors_iff_ne_zero] }
end

variables (K)

lemma is_primitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]}
  (hp : p.is_primitive) (hq : q.is_primitive) :
  (p ∣ q) ↔ (p.map (algebra_map R K) ∣ q.map (algebra_map R K)) :=
⟨λ ⟨a,b⟩, ⟨a.map (algebra_map R K), b.symm ▸ polynomial.map_mul (algebra_map R K)⟩,
  λ h, hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩

end normalized_gcd_monoid

end fraction_map

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem is_primitive.int.irreducible_iff_irreducible_map_cast
  {p : ℤ[X]} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map (int.cast_ring_hom ℚ)) :=
hp.irreducible_iff_irreducible_map_fraction_map

lemma is_primitive.int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X])
  (hp : p.is_primitive) (hq : q.is_primitive) :
  (p ∣ q) ↔ (p.map (int.cast_ring_hom ℚ) ∣ q.map (int.cast_ring_hom ℚ)) :=
hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq

end polynomial
