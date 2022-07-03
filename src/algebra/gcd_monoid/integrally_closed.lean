/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.gcd_monoid.basic
import ring_theory.integrally_closed
import ring_theory.polynomial.scale_roots
import ring_theory.polynomial.eisenstein

/-!

# GCD domains are integrally closed

-/

open_locale big_operators

lemma is_fraction_ring.surj_of_gcd_domain (R : Type*) [comm_ring R] [is_domain R] [gcd_monoid R]
  {K : Type*} [field K] [algebra R K] [is_fraction_ring R K] (z : K) (hz : z ≠ 0) :
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ associated (gcd a b) 1 ∧ algebra_map R K a / algebra_map R K b = z :=
begin
  obtain ⟨x, y, hy, e⟩ : ∃ (x : R), _ := is_fraction_ring.div_surjective z,
  replace hy := mem_non_zero_divisors_iff_ne_zero.mp hy,
  cases eq_or_ne x 0 with hx hx,
  { refine (hz _).elim, rwa [hx, map_zero, zero_div, eq_comm] at e },
  obtain ⟨x', ex⟩ := gcd_dvd_left x y,
  obtain ⟨y', ey⟩ := gcd_dvd_right x y,
  obtain ⟨hg, hx⟩ := ne_zero_and_ne_zero_of_mul (ne_of_eq_of_ne ex.symm hx),
  obtain ⟨-, hy⟩ := ne_zero_and_ne_zero_of_mul (ne_of_eq_of_ne ey.symm hy),
  refine ⟨x', y', hx, hy, _, _⟩,
  { apply associated.of_mul_left _ (associated.refl $ gcd x y) hg,
    convert (gcd_mul_left' (gcd x y) x' y').symm using 1,
    rw [← ex, ← ey, mul_one] },
  { rw [← e, div_eq_div_iff, ← map_mul, ← map_mul, ey, ← mul_assoc, mul_comm x', ← ex],
    all_goals { rw (map_ne_zero_iff _ $ is_fraction_ring.injective R K), assumption } }
end

instance gcd_monoid.to_is_integrally_closed {R : Type*} [comm_ring R] [is_domain R] [gcd_monoid R] :
  is_integrally_closed R :=
begin
  constructor,
  rintro X ⟨p, hp₁, hp₂⟩,
  change X ∈ (algebra_map R (fraction_ring R)).range,
  by_cases hX : X = 0, { rw hX, exact subring.zero_mem _ },
  obtain ⟨x, y, hx, hy, hg, rfl⟩ : ∃ (x : R), _ := is_fraction_ring.surj_of_gcd_domain R X hX,
  have inj := is_fraction_ring.injective R (fraction_ring R),
  have : y ∣ x ^ p.nat_degree,
  { rw [← nat_degree_scale_roots p y, ← ideal.mem_span_singleton],
    refine polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_root_of_monic_mem _ _
      ((monic_scale_roots_iff y).mpr hp₁) _ (le_of_eq rfl),
    { constructor,
      intros i hi,
      rw coeff_scale_roots,
      rw nat_degree_scale_roots at hi,
      refine ideal.mul_mem_left _ _ (ideal.pow_mem_of_mem _
        (ideal.mem_span_singleton.mpr $ dvd_refl _) _ (tsub_pos_of_lt hi)) },
    { have := scale_roots_aeval_eq_zero hp₂,
      rwa [mul_div_cancel' _ ((map_ne_zero_iff _ inj).mpr hy), ← algebra.of_id_apply,
        polynomial.aeval_alg_hom_apply, algebra.of_id_apply, map_eq_zero_iff _ inj] at this } },
  have : is_unit y,
  { rw [is_unit_iff_dvd_one, ← one_pow],
    exact hg.pow_pow.dvd_iff_dvd_right.mp ((gcd_greatest_associated this (dvd_refl y)
      (λ _ _ h, h)).dvd_iff_dvd_left.mpr gcd_pow_left_dvd_pow_gcd) },
  use x * (this.unit⁻¹ : _),
  rw [map_mul, ring_hom.map_units_inv, ← div_eq_mul_inv],
  refl,
end
