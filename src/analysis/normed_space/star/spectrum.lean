/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum
import algebra.star.module
import analysis.normed_space.star.exponential

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/

local postfix `⋆`:std.prec.max_plus := star

open_locale topological_space ennreal
open filter ennreal spectrum cstar_ring

section unitary_spectrum

variables
{𝕜 : Type*} [normed_field 𝕜]
{E : Type*} [normed_ring E] [star_ring E] [cstar_ring E]
[normed_algebra 𝕜 E] [complete_space E] [nontrivial E]

lemma unitary.spectrum_subset_circle (u : unitary E) :
  spectrum 𝕜 (u : E) ⊆ metric.sphere 0 1 :=
begin
  refine λ k hk, mem_sphere_zero_iff_norm.mpr (le_antisymm _ _),
  { simpa only [cstar_ring.norm_coe_unitary u] using norm_le_norm_of_mem hk },
  { rw ←unitary.coe_to_units_apply u at hk,
    have hnk := ne_zero_of_mem_of_unit hk,
    rw [←inv_inv (unitary.to_units u), ←spectrum.map_inv, set.mem_inv] at hk,
    have : ∥k∥⁻¹ ≤ ∥↑((unitary.to_units u)⁻¹)∥, simpa only [norm_inv] using norm_le_norm_of_mem hk,
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this }
end

lemma spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
  spectrum 𝕜 u ⊆ metric.sphere 0 1 :=
unitary.spectrum_subset_circle ⟨u, h⟩

end unitary_spectrum

section complex_scalars

open complex

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [complete_space A] [star_ring A] [cstar_ring A]

local notation `↑ₐ` := algebra_map ℂ A

lemma spectral_radius_eq_nnnorm_of_self_adjoint [norm_one_class A] {a : A}
  (ha : a ∈ self_adjoint A) :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  have hconst : tendsto (λ n : ℕ, (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds,
  refine tendsto_nhds_unique _ hconst,
  convert (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (nat.tendsto_pow_at_top_at_top_of_one_lt (by linarith : 1 < 2)),
  refine funext (λ n, _),
  rw [function.comp_app, nnnorm_pow_two_pow_of_self_adjoint ha, ennreal.coe_pow, ←rpow_nat_cast,
    ←rpow_mul],
  simp,
end

lemma spectral_radius_eq_nnnorm_of_star_normal [norm_one_class A] (a : A) [is_star_normal a] :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  refine (ennreal.pow_strict_mono two_ne_zero).injective _,
  have ha : a⋆ * a ∈ self_adjoint A,
    from self_adjoint.mem_iff.mpr (by simpa only [star_star] using (star_mul a⋆ a)),
  have heq : (λ n : ℕ, ((∥(a⋆ * a) ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞))
    = (λ x, x ^ 2) ∘ (λ n : ℕ, ((∥a ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞)),
  { funext,
    rw [function.comp_apply, ←rpow_nat_cast, ←rpow_mul, mul_comm, rpow_mul, rpow_nat_cast,
      ←coe_pow, sq, ←nnnorm_star_mul_self, commute.mul_pow (star_comm_self' a), star_pow], },
  have h₂ := ((ennreal.continuous_pow 2).tendsto (spectral_radius ℂ a)).comp
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a),
  rw ←heq at h₂,
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a⋆ * a)),
  rw [spectral_radius_eq_nnnorm_of_self_adjoint ha, sq, nnnorm_star_mul_self, coe_mul],
end

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem self_adjoint.mem_spectrum_eq_re [star_module ℂ A] [nontrivial A] {a : A}
  (ha : a ∈ self_adjoint A) {z : ℂ} (hz : z ∈ spectrum ℂ a) : z = z.re :=
begin
  let Iu := units.mk0 I I_ne_zero,
  have : exp ℂ (I • z) ∈ spectrum ℂ (exp ℂ (I • a)),
    by simpa only [units.smul_def, units.coe_mk0]
      using spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz),
  exact complex.ext (of_real_re _)
    (by simpa only [←complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp,
      real.exp_eq_one_iff, smul_eq_mul, I_mul, neg_eq_zero]
      using spectrum.subset_circle_of_unitary (self_adjoint.exp_i_smul_unitary ha) this),
end

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem self_adjoint.mem_spectrum_eq_re' [star_module ℂ A] [nontrivial A]
  (a : self_adjoint A) {z : ℂ} (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
self_adjoint.mem_spectrum_eq_re a.property hz

/-- The spectrum of a selfadjoint is real -/
theorem self_adjoint.coe_re_map_spectrum [star_module ℂ A] [nontrivial A] {a : A}
  (ha : a ∈ self_adjoint A) : spectrum ℂ a = (coe ∘ re '' (spectrum ℂ a) : set ℂ) :=
le_antisymm (λ z hz, ⟨z, hz, (self_adjoint.mem_spectrum_eq_re ha hz).symm⟩) (λ z, by
  { rintros ⟨z, hz, rfl⟩,
    simpa only [(self_adjoint.mem_spectrum_eq_re ha hz).symm, function.comp_app] using hz })

/-- The spectrum of a selfadjoint is real -/
theorem self_adjoint.coe_re_map_spectrum' [star_module ℂ A] [nontrivial A] (a : self_adjoint A) :
  spectrum ℂ (a : A) = (coe ∘ re '' (spectrum ℂ (a : A)) : set ℂ) :=
self_adjoint.coe_re_map_spectrum a.property

end complex_scalars
