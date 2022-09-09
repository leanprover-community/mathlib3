/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum
import algebra.star.module
import analysis.normed_space.star.exponential
import topology.algebra.module.character_space
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

lemma is_self_adjoint.spectral_radius_eq_nnnorm [norm_one_class A] {a : A}
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

lemma is_star_normal.spectral_radius_eq_nnnorm [norm_one_class A] (a : A) [is_star_normal a] :
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
theorem is_self_adjoint.mem_spectrum_eq_re [star_module ℂ A] [nontrivial A] {a : A}
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
theorem self_adjoint.mem_spectrum_eq_re [star_module ℂ A] [nontrivial A]
  (a : self_adjoint A) {z : ℂ} (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
a.prop.mem_spectrum_eq_re hz

/-- The spectrum of a selfadjoint is real -/
theorem is_self_adjoint.coe_re_map_spectrum [star_module ℂ A] [nontrivial A] {a : A}
  (ha : is_self_adjoint a) : spectrum ℂ a = (coe ∘ re '' (spectrum ℂ a) : set ℂ) :=
le_antisymm (λ z hz, ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) (λ z, by
  { rintros ⟨z, hz, rfl⟩,
    simpa only [(ha.mem_spectrum_eq_re hz).symm, function.comp_app] using hz })

/-- The spectrum of a selfadjoint is real -/
theorem self_adjoint.coe_re_map_spectrum [star_module ℂ A] [nontrivial A] (a : self_adjoint A) :
  spectrum ℂ (a : A) = (coe ∘ re '' (spectrum ℂ (a : A)) : set ℂ) :=
a.property.coe_re_map_spectrum

end complex_scalars

namespace star_alg_hom

variables {F A B : Type*}
[normed_ring A] [normed_algebra ℂ A] [norm_one_class A]
[complete_space A] [star_ring A] [cstar_ring A]
[normed_ring B] [normed_algebra ℂ B] [norm_one_class B]
[complete_space B] [star_ring B] [cstar_ring B]
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

open continuous_map

section gelfand_transform

variables (𝕜 A : Type*) [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜]
  [topological_ring 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

/-- The **Gelfand transform** is an algebra homomorphism (over `𝕜`) from a topological `𝕜`-algebra
`A` into the `𝕜`-algebra of continuous `𝕜`-valued functions on the `character_space 𝕜 A`.
The character space itself consists of all algebra homomorphisms from `A` to `𝕜`.  -/
@[simps] def gelfand_transform : A →ₐ[𝕜] C(character_space 𝕜 A, 𝕜) :=
{ to_fun := λ a,
  { to_fun := λ φ, φ a,
    continuous_to_fun := (eval_continuous a).comp continuous_induced_dom },
    map_one' := by {ext, simp only [coe_mk, coe_one, pi.one_apply, map_one a] },
    map_mul' := λ a b, by {ext, simp only [map_mul, coe_mk, coe_mul, pi.mul_apply] },
    map_zero' := by {ext, simp only [map_zero, coe_mk, coe_mul, coe_zero, pi.zero_apply], },
    map_add' :=  λ a b, by {ext, simp only [map_add, coe_mk, coe_add, pi.add_apply] },
    commutes' := λ k, by {ext, simp only [alg_hom_class.commutes, algebra.id.map_eq_id,
      ring_hom.id_apply, coe_mk, algebra_map_apply, algebra.id.smul_eq_mul, mul_one] } }

end gelfand_transform

open complex

section self_skew_adjoint

variables {A : Type*} [add_comm_group A] [module ℂ A] [star_add_monoid A] [star_module ℂ A]

/-- Create a `self_adjoint` element from a `skew_adjoint` element by multiplying by the scalar
`-complex.I`. -/
@[simps] def skew_adjoint.neg_I_smul : skew_adjoint A →ₗ[ℝ] self_adjoint A :=
{ to_fun := λ a, ⟨-I • a, by simp only [self_adjoint.mem_iff, neg_smul, star_neg, star_smul,
    is_R_or_C.star_def, conj_I, skew_adjoint.star_coe_eq, neg_smul_neg]⟩,
  map_add' := λ a b, by { ext, simp only [add_subgroup.coe_add, smul_add, add_mem_class.mk_add_mk] },
  map_smul' := λ a b, by { ext, simp only [neg_smul, skew_adjoint.coe_smul, add_subgroup.coe_mk,
    ring_hom.id_apply, self_adjoint.coe_smul, smul_neg, neg_inj], rw smul_comm, } }

lemma skew_adjoint.I_smul_neg_I (a : skew_adjoint A) :
  I • (skew_adjoint.neg_I_smul a : A) = a :=
by simp only [smul_smul, skew_adjoint.neg_I_smul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
  neg_neg]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`self_adjoint_part ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginary_part`, which doesn't exist in more generic star modules. -/
noncomputable def real_part : A →ₗ[ℝ] self_adjoint A := self_adjoint_part ℝ

@[simp] lemma coe_real_part_apply (a : A) : (real_part a : A) = (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • a⋆ :=
by { unfold real_part, simp only [self_adjoint_part_apply_coe, inv_of_eq_inv, smul_add] }

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `self_adjoint`
and `skew_adjoint` parts, but in a star module over `ℂ` we have
`star_module.real_part_add_I_smul_imaginary_part`, which allows us to decompose into a linear
combination of `self_adjoint`s. -/
noncomputable
def imaginary_part : A →ₗ[ℝ] self_adjoint A := skew_adjoint.neg_I_smul.comp (skew_adjoint_part ℝ)

@[simp] lemma coe_imaginary_part_apply (a : A) :
  (imaginary_part a : A) = -I • ((2 : ℝ)⁻¹ • a - (2 : ℝ)⁻¹ • a⋆) :=
begin
  unfold imaginary_part,
  simp only [linear_map.coe_comp, skew_adjoint.neg_I_smul_apply_coe, skew_adjoint_part_apply_coe,
    inv_of_eq_inv, neg_smul, neg_inj, smul_sub],
end

localized "notation `ℜ` := real_part" in complex_star_module
localized "notation `ℑ` := imaginary_part" in complex_star_module

/-- The standard decomposition of `ℜ a + complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
lemma star_module.real_part_add_I_smul_imaginary_part (a : A) : (ℜ a + I • ℑ a : A) = a :=
by simpa only [smul_smul, coe_real_part_apply, coe_imaginary_part_apply, neg_smul, smul_neg,
  I_mul_I, one_smul, neg_sub, add_add_sub_cancel] using inv_of_two_smul_add_inv_of_two_smul ℝ a

end self_skew_adjoint

open_locale complex_star_module

variables {F A : Type*} [normed_ring A] [normed_algebra ℂ A] [nontrivial A] [complete_space A]
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
    { rw ←star_module.real_part_add_I_smul_imaginary_part a,
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
{ .. hF, .. weak_dual.complex.star_hom_class }

omit hF

variable (A)
/-- The `gelfand_transform` as a `star_alg_hom` when the scalar field is `ℂ`. -/
noncomputable def gelfand_star_transform : A →⋆ₐ[ℂ] C(character_space ℂ A, ℂ) :=
{ map_star' := λ a, continuous_map.ext $
    λ φ, by simp only [alg_hom.to_fun_eq_coe, gelfand_transform_apply_apply, map_star, star_apply],
  .. gelfand_transform ℂ A }
variable {A}

@[simp] lemma gelfand_star_transform_apply_apply (a : A) (φ : character_space ℂ A) :
  gelfand_star_transform A a φ = φ a := rfl

end weak_dual
