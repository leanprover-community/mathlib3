/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum
import algebra.star.module
import analysis.special_functions.exponential

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/

open_locale topological_space ennreal
open filter ennreal spectrum

local postfix `⋆`:std.prec.max_plus := star

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

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [cstar_ring A] [complete_space A]
[measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

lemma spectral_radius_eq_nnnorm_of_self_adjoint {a : A} (ha : a ∈ self_adjoint A) :
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

lemma self_adjoint.coe_spectral_radius_eq_nnnorm (a : self_adjoint A) :
  spectral_radius ℂ (a : A) = ∥(a : A)∥₊ :=
spectral_radius_eq_nnnorm_of_self_adjoint a.property

end complex_scalars


/-- The inclusion of the base field in a algebra as a continuous linear map. -/
@[simps]
def algebra_map_clm (𝕜 : Type*) (E : Type*) [normed_field 𝕜] [semi_normed_ring E]
  [normed_algebra 𝕜 E] : 𝕜 →L[𝕜] E :=
{ to_fun := algebra_map 𝕜 E,
  map_add' := (algebra_map 𝕜 E).map_add,
  map_smul' := λ r x, by rw [algebra.id.smul_eq_mul, map_mul, ring_hom.id_apply, algebra.smul_def],
  cont := (algebra_map_isometry 𝕜 E).continuous }

lemma algebra_map_clm_coe (𝕜 : Type*) (E : Type*) [normed_field 𝕜] [semi_normed_ring E]
  [normed_algebra 𝕜 E] : (algebra_map_clm 𝕜 E : 𝕜 → E) = (algebra_map 𝕜 E : 𝕜 → E) := rfl

lemma star_exp {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A] [normed_algebra 𝕜 A]
  [star_ring A] [cstar_ring A] [complete_space A]
  [star_module 𝕜 A] (a : A) : (exp 𝕜 A a)⋆ = exp 𝕜 A a⋆ :=
begin
  rw exp_eq_tsum,
  have := continuous_linear_map.map_tsum
    (starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A).to_linear_isometry.to_continuous_linear_map
    (exp_series_summable' a),
  dsimp at this,
  convert this,
  funext,
  simp only [star_smul, star_pow, one_div, is_R_or_C.star_def, is_R_or_C.conj_inv, map_nat_cast],
end

lemma algebra_map_exp_comm (𝕜 : Type*) (A : Type*) [is_R_or_C 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] [complete_space A] (z : 𝕜) :
  algebra_map 𝕜 A (exp 𝕜 𝕜 z) = exp 𝕜 A (algebra_map 𝕜 A z) :=
begin
  rw [exp_eq_tsum, exp_eq_tsum, ←algebra_map_clm_coe,
    (algebra_map_clm 𝕜 A).map_tsum (exp_series_summable' z)],
  simp_rw [(algebra_map_clm 𝕜 A).map_smul, algebra_map_clm_coe, map_pow],
end

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [cstar_ring A] [complete_space A]
[star_module ℂ A]

open complex

lemma self_adjoint.exp_i_smul_unitary {a : A} (ha : a ∈ self_adjoint A) :
  exp ℂ A (I • a) ∈ unitary A :=
begin
  rw [unitary.mem_iff, star_exp],
  simp only [star_smul, is_R_or_C.star_def, self_adjoint.mem_iff.mp ha, conj_I, neg_smul],
  rw ←@exp_add_of_commute ℂ A _ _ _ _ _ _ ((commute.refl (I • a)).neg_left),
  rw ←@exp_add_of_commute ℂ A _ _ _ _ _ _ ((commute.refl (I • a)).neg_right),
  simpa only [add_right_neg, add_left_neg, and_self] using (exp_zero : exp ℂ A 0 = 1),
end

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
noncomputable def self_adjoint.exp_unitary (a : self_adjoint A) : unitary A :=
⟨exp ℂ A (I • a), self_adjoint.exp_i_smul_unitary (a.property)⟩

open self_adjoint

lemma commute.exp_unitary_add {a b : self_adjoint A} (h : commute (a : A) (b : A)) :
  exp_unitary (a + b) = exp_unitary a * exp_unitary b :=
begin
  ext,
  have hcomm : commute (I • (a : A)) (I • (b : A)),
  calc _ = _ : by simp only [h.eq, algebra.smul_mul_assoc, algebra.mul_smul_comm],
  simpa only [exp_unitary_coe, add_subgroup.coe_add, smul_add] using exp_add_of_commute hcomm,
end

lemma commute.exp_unitary {a b : self_adjoint A} (h : commute (a : A) (b : A)) :
  commute (exp_unitary a) (exp_unitary b) :=
calc (exp_unitary a) * (exp_unitary b) = (exp_unitary b) * (exp_unitary a)
  : by rw [←h.exp_unitary_add, ←h.symm.exp_unitary_add, add_comm]


local notation `↑ₐ` := algebra_map ℂ A

set_option profiler true

/-- `exp ℂ ℂ` maps the spectrum of `a` into the spectrum of `exp ℂ A a`. -/
theorem spectrum.exp_mem (a : A) {z : ℂ} (hz : z ∈ spectrum ℂ a) :
  exp ℂ ℂ z ∈ spectrum ℂ (exp ℂ A a) :=
begin
  have hexpmul : exp ℂ A a = exp ℂ A (a - ↑ₐ z) * ↑ₐ (exp ℂ ℂ z),
  { rw [algebra_map_exp_comm ℂ A z, ←exp_add_of_commute (algebra.commutes z (a - ↑ₐz)).symm,
      sub_add_cancel] },
  let b := ∑' n : ℕ, ((1 / (n + 1).factorial) : ℂ) • (a - ↑ₐz) ^ n,
  have hb : summable (λ n : ℕ, ((1 / (n + 1).factorial) : ℂ) • (a - ↑ₐz) ^ n),
  { refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial ∥a - ↑ₐz∥) _,
    filter_upwards [eventually_cofinite_ne 0] with n hn,
    field_simp [norm_smul],
    exact div_le_div (pow_nonneg (norm_nonneg _) n) (norm_pow_le' (a - ↑ₐz) (zero_lt_iff.mpr hn))
      (by exact_mod_cast nat.factorial_pos n)
      (by exact_mod_cast nat.factorial_le (lt_add_one n).le) },
  have h₀ : ∑' n : ℕ, ((1 / (n + 1).factorial) : ℂ) • (a - ↑ₐz) ^ (n + 1) = (a - ↑ₐz) * b,
    { simpa only [mul_smul_comm, pow_succ] using hb.tsum_mul_left (a - ↑ₐz) },
  have h₁ : ∑' n : ℕ, ((1 / (n + 1).factorial) : ℂ) • (a - ↑ₐz) ^ (n + 1) = b * (a - ↑ₐz),
    { simpa only [pow_succ', algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐz) },
  have h₃ : exp ℂ A (a - ↑ₐz) = 1 + (a - ↑ₐz) * b,
  { rw exp_eq_tsum,
    convert tsum_eq_zero_add (exp_series_summable' (a - ↑ₐz)),
    simp only [nat.factorial_zero, nat.cast_one, _root_.div_one, pow_zero, one_smul],
    exact h₀.symm },
  rw [spectrum.mem_iff, is_unit.sub_iff, ←one_mul (↑ₐ(exp ℂ ℂ z)), hexpmul, ←_root_.sub_mul,
    commute.is_unit_mul_iff (algebra.commutes (exp ℂ ℂ z) (exp ℂ A (a - ↑ₐz) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, commute.is_unit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐz) * b = b * (a - ↑ₐz))],
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr is_unit.sub_iff).mp hz)),
end

open_locale pointwise

theorem self_adjoint.mem_spectrum_eq_re [nontrivial A] {a : A} (ha : a ∈ self_adjoint A) {z : ℂ}
  (hz : z ∈ spectrum ℂ a) : z = z.re :=
begin
  let Iu := units.mk0 I I_ne_zero,
  have : exp ℂ ℂ (I • z) ∈ spectrum ℂ (exp ℂ A (I • a)),
    by simpa only [units.smul_def, units.coe_mk0]
      using spectrum.exp_mem (Iu • a) (smul_mem_smul_iff.mpr hz),
  exact complex.ext (of_real_re _)
    (by simpa only [←complex.exp_eq_exp_ℂ_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp,
      real.exp_eq_one_iff, smul_eq_mul, I_mul, neg_eq_zero]
      using spectrum.subset_circle_of_unitary (exp_i_smul_unitary ha) this),
end

theorem self_adjoint.coe_re_map_spectrum [nontrivial A] {a : A} (ha : a ∈ self_adjoint A) :
  spectrum ℂ a = (coe ∘ re '' (spectrum ℂ a) : set ℂ) :=
le_antisymm (λ z hz, ⟨z, hz, (self_adjoint.mem_spectrum_eq_re ha hz).symm⟩) (λ z,
  by { rintros ⟨z, hz, rfl⟩,
       simpa only [(self_adjoint.mem_spectrum_eq_re ha hz).symm, function.comp_app] using hz })
