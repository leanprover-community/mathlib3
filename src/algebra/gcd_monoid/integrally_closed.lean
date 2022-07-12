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

open_locale big_operators polynomial

lemma is_localization.surj_of_gcd_domain {R : Type*} [comm_ring R] [is_domain R] [gcd_monoid R]
  (M : submonoid R) {K} [comm_semiring K] [algebra R K] [is_localization M K] (z : K) :
  ∃ a b : R, is_unit (gcd a b) ∧ z * algebra_map R K b = algebra_map R K a :=
begin
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := is_localization.mk'_surjective M z,
  obtain ⟨x', y', d, rfl, rfl, hu⟩ := extract_gcd x y,
  use [x', y', hu],
  rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul],
  convert is_localization.mk'_mul_cancel_left _ _ using 2,
  { rw [← mul_assoc, mul_comm y'], refl }, { apply_instance },
end

lemma dvd_pow_nat_degree_of_eval₂_eq_zero {R A : Type*} [comm_ring R] [comm_ring A] {f : R →+* A}
  (hf : function.injective f) {p : R[X]} (hp : p.monic) (x y : R) (z : A)
  (h0 : p.eval₂ f z = 0) (hz : f x * z = f y) : x ∣ y ^ p.nat_degree :=
begin
  rw [← nat_degree_scale_roots p x, ← ideal.mem_span_singleton],
  refine (scale_roots.is_weakly_eisenstein_at _ (ideal.mem_span_singleton.mpr $ dvd_refl x))
    .pow_nat_degree_le_of_root_of_monic_mem _ ((monic_scale_roots_iff x).mpr hp) _ le_rfl,
  rw injective_iff_map_eq_zero' at hf,
  have := scale_roots_eval₂_eq_zero f h0,
  rwa [hz, polynomial.eval₂_at_apply, hf] at this
end

@[priority 100]
instance gcd_monoid.to_is_integrally_closed {R : Type*} [comm_ring R] [is_domain R] [gcd_monoid R] :
  is_integrally_closed R :=
⟨λ X ⟨p, hp₁, hp₂⟩, begin
  obtain ⟨x, y, hg, he⟩ := is_localization.surj_of_gcd_domain (non_zero_divisors R) X,
  have := dvd_pow_nat_degree_of_eval₂_eq_zero (is_fraction_ring.injective R $ fraction_ring R)
    hp₁ y x _ hp₂ (by rw [mul_comm, he]),
  have : is_unit y,
  { rw [is_unit_iff_dvd_one, ← one_pow],
    exact (dvd_gcd this $ dvd_refl y).trans (gcd_pow_left_dvd_pow_gcd.trans $
      pow_dvd_pow_of_dvd (is_unit_iff_dvd_one.1 hg) _) },
  use x * (this.unit⁻¹ : _),
  erw [map_mul, ← units.coe_map_inv, eq_comm, units.eq_mul_inv_iff_mul_eq],
  exact he,
end⟩
