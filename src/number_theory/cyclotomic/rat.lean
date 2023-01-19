/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import number_theory.cyclotomic.discriminant
import ring_theory.polynomial.eisenstein.is_integral

/-!
# Ring of integers of `p ^ n`-th cyclotomic fields
We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a `p ^ n`-th cyclotomic extension of `ℚ`.

## Main results
* `is_cyclotomic_extension.rat.is_integral_closure_adjoin_singleton_of_prime_pow`: if `K` is a
  `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the integral closure of
  `ℤ` in `K`.
* `is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime_pow`: the integral
  closure of `ℤ` inside `cyclotomic_field (p ^ k) ℚ` is `cyclotomic_ring (p ^ k) ℤ ℚ`.
-/

universes u

open algebra is_cyclotomic_extension polynomial number_field

open_locale cyclotomic number_field nat

variables {p : ℕ+} {k : ℕ} {K : Type u} [field K] [char_zero K] {ζ : K} [hp : fact (p : ℕ).prime]

include hp

namespace is_cyclotomic_extension.rat

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
lemma is_integral_closure_adjoin_singleton_of_prime_pow
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
    { have h₁ := minpoly.is_integrally_closed_eq_field_fractions' ℚ hint,
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp
        (cyclotomic.irreducible_rat (p ^ _).pos),
      rw [is_primitive_root.sub_one_power_basis_gen] at h₁,
      rw [h₁, ← map_cyclotomic_int, show int.cast_ring_hom ℚ = algebra_map ℤ ℚ, by refl,
        show ((X + 1)) = map (algebra_map ℤ ℚ) (X + 1), by simp, ← map_comp] at h₂,
      haveI : char_zero ℚ := strict_ordered_semiring.to_char_zero,
      rw [is_primitive_root.sub_one_power_basis_gen, map_injective (algebra_map ℤ ℚ)
        ((algebra_map ℤ ℚ).injective_int) h₂],
      exact cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at _ _ },
    refine adjoin_le _ (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at
      (nat.prime_iff_prime_int.1 hp.out) hint h H hmin),
    simp only [set.singleton_subset_iff, set_like.mem_coe],
    exact subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (subalgebra.one_mem _) }
end

lemma is_integral_closure_adjoin_singleton_of_prime [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ ↑p) :
  is_integral_closure (adjoin ℤ ({ζ} : set K)) ℤ K :=
begin
  rw [← pow_one p] at hζ hcycl,
  exactI is_integral_closure_adjoin_singleton_of_prime_pow hζ,
end

local attribute [-instance] cyclotomic_field.algebra

/-- The integral closure of `ℤ` inside `cyclotomic_field (p ^ k) ℚ` is
`cyclotomic_ring (p ^ k) ℤ ℚ`. -/
lemma cyclotomic_ring_is_integral_closure_of_prime_pow :
  is_integral_closure (cyclotomic_ring (p ^ k) ℤ ℚ) ℤ (cyclotomic_field (p ^ k) ℚ) :=
begin
  haveI : char_zero ℚ := strict_ordered_semiring.to_char_zero,
  haveI : is_cyclotomic_extension {p ^ k} ℚ (cyclotomic_field (p ^ k) ℚ),
  { convert cyclotomic_field.is_cyclotomic_extension (p ^ k) _,
    { exact subsingleton.elim _ _ },
    { exact ne_zero.char_zero } },
  have hζ := zeta_spec (p ^ k) ℚ (cyclotomic_field (p ^ k) ℚ),
  refine ⟨is_fraction_ring.injective _ _, λ x, ⟨λ h, ⟨⟨x, _⟩, rfl⟩, _⟩⟩,
  { have := (is_integral_closure_adjoin_singleton_of_prime_pow hζ).is_integral_iff,
    obtain ⟨y, rfl⟩ := this.1 h,
    convert adjoin_mono _ y.2,
    { simp only [eq_iff_true_of_subsingleton] },
    { simp only [eq_iff_true_of_subsingleton] },
    { simp only [pnat.pow_coe, set.singleton_subset_iff, set.mem_set_of_eq],
      exact hζ.pow_eq_one } },
  { haveI : is_cyclotomic_extension {p ^ k} ℤ (cyclotomic_ring (p ^ k) ℤ ℚ),
    { convert cyclotomic_ring.is_cyclotomic_extension _ ℤ ℚ,
      { exact subsingleton.elim _ _ },
      { exact ne_zero.char_zero } },
    rintro ⟨y, rfl⟩,
    exact is_integral.algebra_map ((is_cyclotomic_extension.integral {p ^ k} ℤ _) _) }
end

lemma cyclotomic_ring_is_integral_closure_of_prime :
  is_integral_closure (cyclotomic_ring p ℤ ℚ) ℤ (cyclotomic_field p ℚ) :=
begin
  rw [← pow_one p],
  exact cyclotomic_ring_is_integral_closure_of_prime_pow
end

end is_cyclotomic_extension.rat

section power_basis

open is_cyclotomic_extension.rat

namespace is_primitive_root

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p ^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`. -/
@[simps] noncomputable def _root_.is_primitive_root.adjoin_equiv_ring_of_integers
  [hcycl : is_cyclotomic_extension {p ^ k} ℚ K] (hζ : is_primitive_root ζ ↑(p ^ k)) :
  adjoin ℤ ({ζ} : set K) ≃ₐ[ℤ] (𝓞 K) :=
let _ := is_integral_closure_adjoin_singleton_of_prime_pow hζ in
  by exactI (is_integral_closure.equiv ℤ (adjoin ℤ ({ζ} : set K)) K (𝓞 K))

/-- The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance _root_.is_cyclotomic_extension.ring_of_integers
  [is_cyclotomic_extension {p ^ k} ℚ K] : is_cyclotomic_extension {p ^ k} ℤ (𝓞 K) :=
let _ := (zeta_spec (p ^ k) ℚ K).adjoin_is_cyclotomic_extension ℤ in by exactI
  is_cyclotomic_extension.equiv _ ℤ _ ((zeta_spec (p ^ k) ℚ K).adjoin_equiv_ring_of_integers)

/-- The integral `power_basis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k`
cyclotomic extension of `ℚ`. -/
noncomputable def integral_power_basis [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
(adjoin.power_basis' (hζ.is_integral (p ^ k).pos)).map hζ.adjoin_equiv_ring_of_integers

@[simp] lemma integral_power_basis_gen [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) :
  hζ.integral_power_basis.gen = ⟨ζ, hζ.is_integral (p ^ k).pos⟩ :=
subtype.ext $ show algebra_map _ K hζ.integral_power_basis.gen = _, by simpa [integral_power_basis]

@[simp] lemma integral_power_basis_dim [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : hζ.integral_power_basis.dim = φ (p ^ k) :=
by simp [integral_power_basis, ←cyclotomic_eq_minpoly hζ, nat_degree_cyclotomic]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p`-th root of
unity and `K` is a `p`-th cyclotomic extension of `ℚ`. -/
@[simps] noncomputable def _root_.is_primitive_root.adjoin_equiv_ring_of_integers'
  [hcycl : is_cyclotomic_extension {p} ℚ K] (hζ : is_primitive_root ζ p) :
  adjoin ℤ ({ζ} : set K) ≃ₐ[ℤ] (𝓞 K) :=
@adjoin_equiv_ring_of_integers p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

/-- The ring of integers of a `p`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
instance _root_.is_cyclotomic_extension.ring_of_integers'
  [is_cyclotomic_extension {p} ℚ K] : is_cyclotomic_extension {p} ℤ (𝓞 K) :=
let _ := (zeta_spec p ℚ K).adjoin_is_cyclotomic_extension ℤ in by exactI
  is_cyclotomic_extension.equiv _ ℤ _ ((zeta_spec p ℚ K).adjoin_equiv_ring_of_integers')

/-- The integral `power_basis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p`-th
cyclotomic extension of `ℚ`. -/
noncomputable def integral_power_basis' [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : power_basis ℤ (𝓞 K) :=
@integral_power_basis p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

@[simp] lemma integral_power_basis'_gen [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : hζ.integral_power_basis'.gen = ⟨ζ, hζ.is_integral p.pos⟩ :=
@integral_power_basis_gen p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

@[simp] lemma power_basis_int'_dim [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : hζ.integral_power_basis'.dim = φ p :=
by erw [@integral_power_basis_dim p 1 K _ _ _ _ (by { convert hcycl, rw pow_one })
  (by rwa pow_one), pow_one]

/-- The integral `power_basis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def sub_one_integral_power_basis [is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
power_basis.of_gen_mem_adjoin' hζ.integral_power_basis (is_integral_of_mem_ring_of_integers $
  subalgebra.sub_mem _ (hζ.is_integral (p ^ k).pos) (subalgebra.one_mem _))
begin
  simp only [integral_power_basis_gen],
  convert subalgebra.add_mem _
    (self_mem_adjoin_singleton ℤ (⟨ζ - 1, _⟩ : 𝓞 K))
    (subalgebra.one_mem _),
  simp
end

@[simp] lemma sub_one_integral_power_basis_gen [is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) :
  hζ.sub_one_integral_power_basis.gen =
  ⟨ζ - 1, subalgebra.sub_mem _ (hζ.is_integral (p ^ k).pos) (subalgebra.one_mem _)⟩ :=
by simp [sub_one_integral_power_basis]

/-- The integral `power_basis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p`-th cyclotomic
extension of `ℚ`. -/
noncomputable def sub_one_integral_power_basis' [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : power_basis ℤ (𝓞 K) :=
@sub_one_integral_power_basis p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

@[simp] lemma sub_one_integral_power_basis'_gen [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) :
  hζ.sub_one_integral_power_basis'.gen =
  ⟨ζ - 1, subalgebra.sub_mem _ (hζ.is_integral p.pos) (subalgebra.one_mem _)⟩ :=
@sub_one_integral_power_basis_gen p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

end is_primitive_root

end power_basis
