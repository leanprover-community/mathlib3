/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum
import analysis.normed_space.star.exponential
import analysis.special_functions.exponential
import algebra.star.star_alg_hom

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/

local postfix `⋆`:std.prec.max_plus := star

section

open_locale topological_space ennreal
open filter ennreal spectrum cstar_ring

section unitary_spectrum

variables
{𝕜 : Type*} [normed_field 𝕜]
{E : Type*} [normed_ring E] [star_ring E] [cstar_ring E]
[normed_algebra 𝕜 E] [complete_space E]

lemma unitary.spectrum_subset_circle (u : unitary E) :
  spectrum 𝕜 (u : E) ⊆ metric.sphere 0 1 :=
begin
  nontriviality E,
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

lemma is_self_adjoint.spectral_radius_eq_nnnorm {a : A}
  (ha : is_self_adjoint a) :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  have hconst : tendsto (λ n : ℕ, (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds,
  refine tendsto_nhds_unique _ hconst,
  convert (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two),
  refine funext (λ n, _),
  rw [function.comp_app, ha.nnnorm_pow_two_pow, ennreal.coe_pow, ←rpow_nat_cast,
    ←rpow_mul],
  simp,
end

lemma is_star_normal.spectral_radius_eq_nnnorm (a : A) [is_star_normal a] :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  refine (ennreal.pow_strict_mono two_ne_zero).injective _,
  have heq : (λ n : ℕ, ((∥(a⋆ * a) ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞))
    = (λ x, x ^ 2) ∘ (λ n : ℕ, ((∥a ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞)),
  { funext,
    rw [function.comp_apply, ←rpow_nat_cast, ←rpow_mul, mul_comm, rpow_mul, rpow_nat_cast,
      ←coe_pow, sq, ←nnnorm_star_mul_self, commute.mul_pow (star_comm_self' a), star_pow], },
  have h₂ := ((ennreal.continuous_pow 2).tendsto (spectral_radius ℂ a)).comp
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a),
  rw ←heq at h₂,
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a⋆ * a)),
  rw [(is_self_adjoint.star_mul_self a).spectral_radius_eq_nnnorm, sq, nnnorm_star_mul_self,
    coe_mul],
end

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem is_self_adjoint.mem_spectrum_eq_re [star_module ℂ A] {a : A}
  (ha : is_self_adjoint a) {z : ℂ} (hz : z ∈ spectrum ℂ a) : z = z.re :=
begin
  let Iu := units.mk0 I I_ne_zero,
  have : exp ℂ (I • z) ∈ spectrum ℂ (exp ℂ (I • a)),
    by simpa only [units.smul_def, units.coe_mk0]
      using spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz),
  exact complex.ext (of_real_re _)
    (by simpa only [←complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp,
      real.exp_eq_one_iff, smul_eq_mul, I_mul, neg_eq_zero]
      using spectrum.subset_circle_of_unitary ha.exp_i_smul_unitary this),
end

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem self_adjoint.mem_spectrum_eq_re [star_module ℂ A]
  (a : self_adjoint A) {z : ℂ} (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
a.prop.mem_spectrum_eq_re hz

/-- The spectrum of a selfadjoint is real -/
theorem is_self_adjoint.coe_re_map_spectrum [star_module ℂ A] {a : A}
  (ha : is_self_adjoint a) : spectrum ℂ a = (coe ∘ re '' (spectrum ℂ a) : set ℂ) :=
le_antisymm (λ z hz, ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) (λ z, by
  { rintros ⟨z, hz, rfl⟩,
    simpa only [(ha.mem_spectrum_eq_re hz).symm, function.comp_app] using hz })

/-- The spectrum of a selfadjoint is real -/
theorem self_adjoint.coe_re_map_spectrum [star_module ℂ A] (a : self_adjoint A) :
  spectrum ℂ (a : A) = (coe ∘ re '' (spectrum ℂ (a : A)) : set ℂ) :=
a.property.coe_re_map_spectrum

end complex_scalars

namespace star_alg_hom

variables {F A B : Type*}
[normed_ring A] [normed_algebra ℂ A] [complete_space A] [star_ring A] [cstar_ring A]
[normed_ring B] [normed_algebra ℂ B] [complete_space B] [star_ring B] [cstar_ring B]
[hF : star_alg_hom_class F ℂ A B] (φ : F)
include hF

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
lemma nnnorm_apply_le (a : A) : ∥(φ a : B)∥₊ ≤ ∥a∥₊ :=
begin
  suffices : ∀ s : A, is_self_adjoint s → ∥φ s∥₊ ≤ ∥s∥₊,
  { exact nonneg_le_nonneg_of_sq_le_sq zero_le'
      (by simpa only [nnnorm_star_mul_self, map_star, map_mul]
      using this _ (is_self_adjoint.star_mul_self a)) },
  { intros s hs,
    simpa only [hs.spectral_radius_eq_nnnorm, (hs.star_hom_apply φ).spectral_radius_eq_nnnorm,
      coe_le_coe] using (show spectral_radius ℂ (φ s) ≤ spectral_radius ℂ s,
      from supr_le_supr_of_subset (alg_hom.spectrum_apply_subset φ s)) }
end

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
lemma norm_apply_le (a : A) : ∥(φ a : B)∥ ≤ ∥a∥ := nnnorm_apply_le φ a

/-- Star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
@[priority 100]
noncomputable instance : continuous_linear_map_class F ℂ A B :=
{ map_continuous := λ φ, add_monoid_hom_class.continuous_of_bound φ 1
    (by simpa only [one_mul] using nnnorm_apply_le φ),
  .. alg_hom_class.linear_map_class }

end star_alg_hom

end

namespace weak_dual

open continuous_map complex
open_locale complex_star_module

variables {F A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
  [star_ring A] [cstar_ring A] [star_module ℂ A] [hF : alg_hom_class F ℂ A ℂ]

include hF

/-- This instance is provided instead of `star_alg_hom_class` to avoid type class inference loops.
See note [lower instance priority] -/
@[priority 100]
noncomputable instance : star_hom_class F A ℂ :=
{ coe := λ φ, φ,
  coe_injective' := fun_like.coe_injective',
  map_star := λ φ a,
  begin
    suffices hsa : ∀ s : self_adjoint A, (φ s)⋆ = φ s,
    { rw ←real_part_add_I_smul_imaginary_part a,
      simp only [map_add, map_smul, star_add, star_smul, hsa, self_adjoint.star_coe_eq] },
    { intros s,
      have := alg_hom.apply_mem_spectrum φ (s : A),
      rw self_adjoint.coe_re_map_spectrum s at this,
      rcases this with ⟨⟨_, _⟩, _, heq⟩,
      rw [←heq, is_R_or_C.star_def, is_R_or_C.conj_of_real] }
  end }

/-- This is not an instance to avoid type class inference loops. See
`weak_dual.complex.star_hom_class`. -/
noncomputable def _root_.alg_hom_class.star_alg_hom_class : star_alg_hom_class F ℂ A ℂ :=
{ coe := λ f, f,
  .. weak_dual.complex.star_hom_class,
  .. hF }

omit hF

namespace character_space

noncomputable instance : star_alg_hom_class (character_space ℂ A) ℂ A ℂ :=
{ coe := λ f, f,
  .. alg_hom_class.star_alg_hom_class }

end character_space

end weak_dual
