/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import number_theory.cyclotomic.discriminant
import ring_theory.polynomial.eisenstein

/-!
# Ring of integers of `p ^ n`-th cyclotomic fields
We compute the ring of integers of a `p ^ n`-th cyclotomic extension of `ℚ`.

## Main results
* `is_cyclotomic_extension.rat.is_integral_closure_adjoing_singleton_of_prime_pow`: if `K` is a
  `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the integral closure of
  `ℤ` in `K`.
* `is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime_pow`: the integral
  closure of `ℤ` inside `cyclotomic_field (p ^ k) ℚ` is `cyclotomic_ring (p ^ k) ℤ ℚ`.
-/

universes u

open algebra is_cyclotomic_extension polynomial

open_locale cyclotomic

namespace is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} {K : Type u} [field K] [char_zero K] {ζ : K} [hp : fact (p : ℕ).prime]

include hp

/-- The discriminant of the power basis given by `ζ - 1`. -/
lemma discr_prime_pow_ne_two' [is_cyclotomic_extension {p ^ (k + 1)} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hk : p ^ (k + 1) ≠ 2) :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis =
  (-1) ^ (((p ^ (k + 1) : ℕ).totient) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
begin
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (p ^ (k + 1)).pos) hk],
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
end

lemma discr_odd_prime' [is_cyclotomic_extension {p} ℚ K] (hζ : is_primitive_root ζ p)
  (hodd : p ≠ 2) :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd],
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
end

/-- The discriminant of the power basis given by `ζ - 1`. Beware that in the cases `p ^ k = 1` and
`p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform
result. See also `is_cyclotomic_extension.rat.discr_prime_pow_eq_unit_mul_pow'`. -/
lemma discr_prime_pow' [is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis =
  (-1) ^ (((p ^ k : ℕ).totient) / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) :=
begin
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (p ^ k).pos)],
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
end

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of the power basis given by `ζ - 1` is `u * p ^ n`. Often this is
enough and less cumbersome to use than `is_cyclotomic_extension.rat.discr_prime_pow'`. -/
lemma discr_prime_pow_eq_unit_mul_pow' [is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) :
  ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.sub_one_power_basis ℚ).basis = u * p ^ n :=
begin
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm],
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (p ^ k).pos)
end

/-- If `K` is a `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the
integral closure of `ℤ` in `K`. -/
lemma is_integral_closure_adjoing_singleton_of_prime_pow
  [hcycl : is_cyclotomic_extension {p ^ k} ℚ K] (hζ : is_primitive_root ζ ↑(p ^ k)) :
  is_integral_closure (adjoin ℤ ({ζ} : set K)) ℤ K :=
begin
  refine ⟨subtype.val_injective, λ x, ⟨λ h, ⟨⟨x, _⟩, rfl⟩, _⟩⟩,
  swap,
  { rintro ⟨y, rfl⟩,
    exact is_integral.algebra_map (le_integral_closure_iff_is_integral.1
      (adjoin_le_integral_closure (hζ.is_integral (p ^ k).pos)) _) },
  let B := hζ.sub_one_power_basis ℚ,
  have hint : is_integral ℤ B.gen :=  is_integral_sub (hζ.is_integral (p ^ k).pos)
    is_integral_one,
  have H := discr_mul_is_integral_mem_adjoin ℚ hint h,
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ,
  rw [hun] at H,
  replace H := subalgebra.smul_mem _ H u.inv,
  rw [← smul_assoc, ← smul_mul_assoc, units.inv_eq_coe_inv, coe_coe, zsmul_eq_mul,
    ← int.cast_mul, units.inv_mul, int.cast_one, one_mul,
    show (p : ℚ) ^ n • x = ((p : ℕ) : ℤ) ^ n • x, by simp [smul_def]] at H,
  unfreezingI { cases k },
  { haveI : is_cyclotomic_extension {1} ℚ K := by simpa using hcycl,
    have : x ∈ (⊥ : subalgebra ℚ K),
    { rw [singleton_one ℚ K],
      exact mem_top },
    obtain ⟨y, rfl⟩ := mem_bot.1 this,
    replace h := (is_integral_algebra_map_iff (algebra_map ℚ K).injective).1 h,
    obtain ⟨z, hz⟩ := is_integrally_closed.is_integral_iff.1 h,
    rw [← hz, ← is_scalar_tower.algebra_map_apply],
    exact subalgebra.algebra_map_mem  _ _ },
  { have hmin : (minpoly ℤ B.gen).is_eisenstein_at (submodule.span ℤ {((p : ℕ) : ℤ)}),
    { have h₁ := minpoly.gcd_domain_eq_field_fractions' ℚ hint,
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp
        (cyclotomic.irreducible_rat (p ^ _).pos),
      rw [is_primitive_root.sub_one_power_basis_gen] at h₁,
      rw [h₁, ← map_cyclotomic_int, show int.cast_ring_hom ℚ = algebra_map ℤ ℚ, by refl,
        show ((X + 1)) = map (algebra_map ℤ ℚ) (X + 1), by simp, ← map_comp] at h₂,
      haveI : char_zero ℚ := ordered_semiring.to_char_zero,
      rw [is_primitive_root.sub_one_power_basis_gen, map_injective (algebra_map ℤ ℚ)
        ((algebra_map ℤ ℚ).injective_int) h₂],
      exact cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at _ _ },
    refine adjoin_le _ (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at
      (nat.prime_iff_prime_int.1 hp.out) hint h H hmin),
    simp only [set.singleton_subset_iff, set_like.mem_coe],
    exact subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (subalgebra.one_mem _) }
end

lemma is_integral_closure_adjoing_singleton_of_prime [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ ↑p) :
  is_integral_closure (adjoin ℤ ({ζ} : set K)) ℤ K :=
begin
  rw [← pow_one p] at hζ hcycl,
  exactI is_integral_closure_adjoing_singleton_of_prime_pow hζ,
end

/-- The integral closure of `ℤ` inside `cyclotomic_field (p ^ k) ℚ` is
`cyclotomic_ring (p ^ k) ℤ ℚ`. -/
lemma cyclotomic_ring_is_integral_closure_of_prime_pow :
  is_integral_closure (cyclotomic_ring (p ^ k) ℤ ℚ) ℤ (cyclotomic_field (p ^ k) ℚ) :=
begin
  haveI : char_zero ℚ := ordered_semiring.to_char_zero,
  have hζ := zeta_spec (p ^ k) ℚ (cyclotomic_field (p ^ k) ℚ),
  refine ⟨is_fraction_ring.injective _ _, λ x, ⟨λ h, ⟨⟨x, _⟩, rfl⟩, _⟩⟩,
  { have := (is_integral_closure_adjoing_singleton_of_prime_pow hζ).is_integral_iff,
    obtain ⟨y, rfl⟩ := this.1 h,
    refine adjoin_mono _ y.2,
    simp only [pnat.pow_coe, set.singleton_subset_iff, set.mem_set_of_eq],
    exact hζ.pow_eq_one },
  { rintro ⟨y, rfl⟩,
    exact is_integral.algebra_map ((is_cyclotomic_extension.integral {p ^ k} ℤ _) _) }
end

lemma cyclotomic_ring_is_integral_closure_of_prime :
  is_integral_closure (cyclotomic_ring p ℤ ℚ) ℤ (cyclotomic_field p ℚ) :=
begin
  rw [← pow_one p],
  exact cyclotomic_ring_is_integral_closure_of_prime_pow
end

end is_cyclotomic_extension.rat
