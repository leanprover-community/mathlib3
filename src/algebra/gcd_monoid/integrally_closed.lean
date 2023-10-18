/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.gcd_monoid.basic
import ring_theory.integrally_closed
import ring_theory.polynomial.eisenstein.basic

/-!

# GCD domains are integrally closed

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open_locale big_operators polynomial

variables {R A : Type*} [comm_ring R] [is_domain R] [gcd_monoid R] [comm_ring A] [algebra R A]

lemma is_localization.surj_of_gcd_domain (M : submonoid R) [is_localization M A] (z : A) :
  ∃ a b : R, is_unit (gcd a b) ∧ z * algebra_map R A b = algebra_map R A a :=
begin
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := is_localization.mk'_surjective M z,
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y,
  use [x', y', hu],
  rw [mul_comm, is_localization.mul_mk'_eq_mk'_of_mul],
  convert is_localization.mk'_mul_cancel_left _ _ using 2,
  { rw [subtype.coe_mk, hy', ← mul_comm y', mul_assoc], conv_lhs { rw hx' } },
  { apply_instance },
end

@[priority 100]
instance gcd_monoid.to_is_integrally_closed : is_integrally_closed R :=
⟨λ X ⟨p, hp₁, hp₂⟩, begin
  obtain ⟨x, y, hg, he⟩ := is_localization.surj_of_gcd_domain (non_zero_divisors R) X,
  have := polynomial.dvd_pow_nat_degree_of_eval₂_eq_zero
    (is_fraction_ring.injective R $ fraction_ring R) hp₁ y x _ hp₂ (by rw [mul_comm, he]),
  have : is_unit y,
  { rw [is_unit_iff_dvd_one, ← one_pow],
    exact (dvd_gcd this $ dvd_refl y).trans (gcd_pow_left_dvd_pow_gcd.trans $
      pow_dvd_pow_of_dvd (is_unit_iff_dvd_one.1 hg) _) },
  use x * (this.unit⁻¹ : _),
  erw [map_mul, ← units.coe_map_inv, eq_comm, units.eq_mul_inv_iff_mul_eq],
  exact he,
end⟩
