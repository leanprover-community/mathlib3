/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.fourier.add_circle

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

We define Fourier transforms in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is an additive character of `𝕜`, i.e. a homomorphism `(multiplicative 𝕜) →* ℂ`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, the Fourier transform is a map from functions `V → E` to
functions `W → E`, defined by sending `f` to

`λ w, ∫ v in V, e (multiplicative.of_add (-L(v, w)) • f v ∂μ`.

The most familiar case, of course, is
* `𝕜 = V = W = ℝ`
* `L = linear_map.mul ℝ ℝ`
* `μ = volume`
* `e = fourier_char` (defined below), i.e. the character `λ x, exp (2 * π * I * x)`.

The notation `𝓕` is available in the locale `fourier_transform` as a shortcut for this case.
However, we set things up much more generally (number theorists care about the case when `𝕜` is an
adele ring, for instance).

## Main results

At present the only nontrivial lemma we prove is `continuous_fourier_transform`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/

noncomputable theory

open measure_theory filter

open_locale topology

section defs

variables
  {𝕜 : Type*} [comm_ring 𝕜]
  {V : Type*} [add_comm_group V] [module 𝕜 V] [measurable_space V]
  {W : Type*} [add_comm_group W] [module 𝕜 W]
  {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]

/-- The Fourier transform of `f : V → E`, with respect to a bilinear form `L : V × W → 𝕜` and an
additive character `e`. -/
def fourier_transform
  (e : (multiplicative 𝕜) →* ℂ)
  (μ : measure V)
  (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
  (f : V → E) (w : W) : E :=
∫ v, e (multiplicative.of_add (-L v w)) • f v ∂μ

lemma fourier_transform.smul
  (e : (multiplicative 𝕜) →* ℂ) (μ : measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
  (f : V → E) (r : ℂ) :
  fourier_transform e μ L (r • f) = r • (fourier_transform e μ L f) :=
begin
  ext1 w,
  dsimp only [pi.smul_apply, fourier_transform],
  simp_rw [smul_comm _ r, integral_smul]
end

/-- A map to a normed space is *unitary* if its values have norm 1. -/
def is_unitary {α β : Type*} [has_norm β] (e : α → β) : Prop :=
∀ (x : α), ‖e x‖ = 1

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
lemma fourier_transform_norm_le {e : (multiplicative 𝕜) →* ℂ} {μ : measure V}
  (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (he' : is_unitary e) {f : V → E} (hf : integrable f μ) (w : W) :
  ‖fourier_transform e μ L f w‖ ≤ ‖mem_ℒp.to_Lp f (mem_ℒp_one_iff_integrable.mpr hf)‖ :=
begin
  rw [Lp.norm_to_Lp, mem_ℒp.snorm_eq_integral_rpow_norm one_ne_zero ennreal.one_ne_top
    (mem_ℒp_one_iff_integrable.mpr hf)],
  have : (1 : ennreal).to_real = 1 := by refl,
  simp_rw [this, inv_one, real.rpow_one],
  rw ennreal.to_real_of_real,
  swap, exact (integral_nonneg (λ _, norm_nonneg _)),
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq _),
  congr' 1 with x:1,
  rw [norm_smul, he', one_mul],
end

end defs

section continuous
-- In this section we assume 𝕜, V, W have topologies, and L, e are continuous (but f needn't be).

variables
  {𝕜 : Type*} [comm_ring 𝕜] [topological_space 𝕜] [topological_ring 𝕜]
  {V : Type*} [add_comm_group V] [module 𝕜 V] [measurable_space V]
    [topological_space V] [opens_measurable_space V]
  {W : Type*} [add_comm_group W] [module 𝕜 W] [topological_space W]
  {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]
  {e : (multiplicative 𝕜) →* ℂ} {μ : measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- If `f` is integrable (and the additive character is unitary), then the Fourier
transform integral is convergent, for all `w`. -/
lemma fourier_integral_convergent
  (he : continuous e) (he' : is_unitary e)
  (hL : continuous (λ p : V × W, L p.1 p.2))
  {f : V → E} (hf : integrable f μ) (w : W) :
  integrable (λ (v : V), e (multiplicative.of_add (-L v w)) • f v) μ :=
begin
  have c : continuous (λ v, e (multiplicative.of_add (-L v w))),
  { refine he.comp (continuous_of_add.comp (continuous.neg _)),
    exact hL.comp (continuous_prod_mk.mpr ⟨continuous_id, continuous_const⟩) },
  rw ←integrable_norm_iff (c.ae_strongly_measurable.smul hf.1),
  convert hf.norm,
  ext1 v,
  rw [norm_smul, he' _, one_mul]
end

variables [complete_space E]

lemma fourier_transform.add
  (he : continuous e) (he' : is_unitary e) (hL : continuous (λ p : V × W, L p.1 p.2))
  {f g : V → E} (hf : integrable f μ) (hg : integrable g μ) :
  (fourier_transform e μ L f) + (fourier_transform e μ L g) = fourier_transform e μ L (f + g) :=
begin
  ext1 w,
  dsimp only [pi.add_apply, fourier_transform],
  simp_rw smul_add,
  rw integral_add,
  { exact fourier_integral_convergent he he' hL hf w },
  { exact fourier_integral_convergent he he' hL hg w },
end

/-- The Fourier transform of an `L^1` function is a continuous function. -/
lemma fourier_transform_continuous [topological_space.first_countable_topology W]
  (he : continuous e) (he' : is_unitary e) (hL : continuous (λ p : V × W, L p.1 p.2))
  {f : V → E} (hf : integrable f μ) :
  continuous (fourier_transform e μ L f) :=
begin
  apply continuous_of_dominated,
  { exact λ w, (fourier_integral_convergent he he' hL hf w).1 },
  { refine λ w, ae_of_all _ (λ v, _),
    { exact λ v, ‖f v‖ },
    { rw [norm_smul, he', one_mul] } },
  { exact hf.norm },
  { refine ae_of_all _ (λ v, (he.comp (continuous_of_add.comp _)).smul continuous_const),
    refine (hL.comp (continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩)).neg }
end

end continuous

section real
open_locale real

/-- The standard additive character of `ℝ`, given by `λ x, exp (2 * π * I * x)`. -/
def fourier_char : (multiplicative ℝ) →* ℂ :=
{ to_fun := (λ z, fourier 1 (z.to_add : unit_add_circle)),
  map_one' := by rw [to_add_one, quotient_add_group.coe_zero, fourier_eval_zero],
  map_mul' := λ x y, by rw [to_add_mul, fourier_coe_apply, complex.of_real_add, mul_add, add_div,
    complex.exp_add, ←fourier_coe_apply, ←fourier_coe_apply] }

lemma fourier_char_apply (x : ℝ) :
  fourier_char (multiplicative.of_add x) = complex.exp (2 * π * complex.I * x) :=
by rw [fourier_char, monoid_hom.coe_mk, to_add_of_add, fourier_coe_apply,
    complex.of_real_one, int.cast_one, mul_one, div_one]

lemma fourier_transform_eq_integral_exp_smul
  {V : Type*} [add_comm_group V] [module ℝ V] [measurable_space V]
  {W : Type*} [add_comm_group W] [module ℝ W]
  {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]
  (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : measure V) (f : V → E) (w : W) :
  fourier_transform fourier_char μ L f w
  = ∫ (v : V), complex.exp (-2 * π * complex.I * L v w) • f v ∂μ :=
begin
  simp_rw [fourier_transform, fourier_char_apply, complex.of_real_neg],
  congr' 1 with v:1,
  congr' 2,
  ring,
end

lemma fourier_transform_mul_eq_integral_exp_smul
  {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]
  (μ : measure ℝ) (f : ℝ → E) (w : ℝ) :
  fourier_transform fourier_char μ (linear_map.mul ℝ ℝ) f w
  = ∫ (v : ℝ), complex.exp (-2 * π * complex.I * v * w) • f v ∂μ :=
by simp_rw [fourier_transform_eq_integral_exp_smul, linear_map.mul_apply', complex.of_real_mul,
  ←mul_assoc]

localized "notation `𝓕` := fourier_transform fourier_char measure_theory.measure_space.volume
  (linear_map.mul ℝ ℝ)" in fourier_transform

lemma is_unitary_fourier_char : is_unitary fourier_char :=
λ x, by rw [fourier_char, monoid_hom.coe_mk, fourier_apply_norm]

@[continuity]
lemma continuous_fourier_char : continuous fourier_char :=
(map_continuous (fourier 1)).comp (continuous_quotient_mk.comp continuous_to_add)

end real
