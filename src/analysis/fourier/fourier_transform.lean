/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.special_functions.complex.circle
import measure_theory.group.integration
import measure_theory.integral.integral_eq_improper

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

In namespace `vector_fourier`, we define the Fourier integral in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is a unitary additive character of `𝕜`, i.e. a homomorphism `(multiplicative 𝕜) →* circle`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, we define `fourier_integral` to be the map from functions `V → E` to
functions `W → E` that sends `f` to

`λ w, ∫ v in V, e [-L v w] • f v ∂μ`,

where `e [x]` is notational sugar for `(e (multiplicative.of_add x) : ℂ)` (available in locale
`fourier_transform`). This includes the cases `W` is the dual of `V` and `L` is the canonical
pairing, or `W = V` and `L` is a bilinear form (e.g. an inner product).

In namespace `fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `real.fourier_char`, i.e. the character `λ x, exp ((2 * π * x) * I)`. The Fourier integral
in this case is defined as `real.fourier_integral`.

## Main results

At present the only nontrivial lemma we prove is `continuous_fourier_integral`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/

noncomputable theory

local notation `𝕊` := circle

open measure_theory filter

open_locale topology

-- To avoid messing around with multiplicative vs. additive characters, we make a notation.
localized "notation e `[` x `]` := (e (multiplicative.of_add x) : ℂ)" in fourier_transform

/-! ## Fourier theory for functions on general vector spaces -/
namespace vector_fourier

variables
  {𝕜 : Type*} [comm_ring 𝕜]
  {V : Type*} [add_comm_group V] [module 𝕜 V] [measurable_space V]
  {W : Type*} [add_comm_group W] [module 𝕜 W]
  {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]

section defs

variables [complete_space E]

/-- The Fourier transform integral for `f : V → E`, with respect to a bilinear form `L : V × W → 𝕜`
and an additive character `e`. -/
def fourier_integral
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
  (f : V → E) (w : W) : E :=
∫ v, e [-L v w] • f v ∂μ

lemma fourier_integral_smul_const
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
  (f : V → E) (r : ℂ) :
  fourier_integral e μ L (r • f) = r • (fourier_integral e μ L f) :=
begin
  ext1 w,
  simp only [pi.smul_apply, fourier_integral, smul_comm _ r, integral_smul],
end

/-- The uniform norm of the Fourier integral of `f` is bounded by the `L¹` norm of `f`. -/
lemma fourier_integral_norm_le (e : (multiplicative 𝕜) →* 𝕊) {μ : measure V}
  (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) {f : V → E} (hf : integrable f μ) (w : W) :
  ‖fourier_integral e μ L f w‖ ≤ ‖hf.to_L1 f‖ :=
begin
  rw L1.norm_of_fun_eq_integral_norm,
  refine (norm_integral_le_integral_norm _).trans (le_of_eq _),
  simp_rw [norm_smul, complex.norm_eq_abs, abs_coe_circle, one_mul],
end

/-- The Fourier integral converts right-translation into scalar multiplication by a phase factor.-/
lemma fourier_integral_comp_add_right [has_measurable_add V]
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure V) [μ.is_add_right_invariant]
  (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (v₀ : V) :
  fourier_integral e μ L (f ∘ (λ v, v + v₀)) = λ w, e [L v₀ w] • fourier_integral e μ L f w :=
begin
  ext1 w,
  dsimp only [fourier_integral, function.comp_apply],
  conv in (L _) { rw ←add_sub_cancel v v₀ },
  rw integral_add_right_eq_self (λ (v : V), e [-L (v - v₀) w] • f v),
  swap, apply_instance,
  dsimp only,
  rw ←integral_smul,
  congr' 1 with v,
  rw [←smul_assoc, smul_eq_mul, ←submonoid.coe_mul, ←e.map_mul, ←of_add_add, ←linear_map.neg_apply,
    ←sub_eq_add_neg, ←linear_map.sub_apply, linear_map.map_sub, neg_sub]
end

end defs

section continuous
/- In this section we assume 𝕜, V, W have topologies, and L, e are continuous (but f needn't be).
   This is used to ensure that `e [-L v w]` is (ae strongly) measurable. We could get away with
   imposing only a measurable-space structure on 𝕜 (it doesn't have to be the Borel sigma-algebra of
   a topology); but it seems hard to imagine cases where this extra generality would be useful, and
   allowing it would complicate matters in the most important use cases.
-/

variables [topological_space 𝕜] [topological_ring 𝕜] [topological_space V] [borel_space V]
  [topological_space W] {e : (multiplicative 𝕜) →* 𝕊} {μ : measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- If `f` is integrable, then the Fourier integral is convergent for all `w`. -/
lemma fourier_integral_convergent
  (he : continuous e) (hL : continuous (λ p : V × W, L p.1 p.2))
  {f : V → E} (hf : integrable f μ) (w : W) :
  integrable (λ (v : V), (e [-L v w]) • f v) μ :=
begin
  rw continuous_induced_rng at he,
  have c : continuous (λ v, e[-L v w]),
  { refine he.comp (continuous_of_add.comp (continuous.neg _)),
    exact hL.comp (continuous_prod_mk.mpr ⟨continuous_id, continuous_const⟩) },
  rw ←integrable_norm_iff (c.ae_strongly_measurable.smul hf.1),
  convert hf.norm,
  ext1 v,
  rw [norm_smul, complex.norm_eq_abs, abs_coe_circle, one_mul]
end

variables [complete_space E]

lemma fourier_integral_add
  (he : continuous e) (hL : continuous (λ p : V × W, L p.1 p.2))
  {f g : V → E} (hf : integrable f μ) (hg : integrable g μ) :
  (fourier_integral e μ L f) + (fourier_integral e μ L g) = fourier_integral e μ L (f + g) :=
begin
  ext1 w,
  dsimp only [pi.add_apply, fourier_integral],
  simp_rw smul_add,
  rw integral_add,
  { exact fourier_integral_convergent he hL hf w },
  { exact fourier_integral_convergent he hL hg w },
end

/-- The Fourier integral of an `L^1` function is a continuous function. -/
lemma fourier_integral_continuous [topological_space.first_countable_topology W]
  (he : continuous e) (hL : continuous (λ p : V × W, L p.1 p.2))
  {f : V → E} (hf : integrable f μ) :
  continuous (fourier_integral e μ L f) :=
begin
  apply continuous_of_dominated,
  { exact λ w, (fourier_integral_convergent he hL hf w).1 },
  { refine λ w, ae_of_all _ (λ v, _),
    { exact λ v, ‖f v‖ },
    { rw [norm_smul, complex.norm_eq_abs, abs_coe_circle, one_mul] } },
  { exact hf.norm },
  { rw continuous_induced_rng at he,
    refine ae_of_all _ (λ v, (he.comp (continuous_of_add.comp _)).smul continuous_const),
    refine (hL.comp (continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩)).neg }
end

end continuous

end vector_fourier

/-! ## Fourier theory for functions on `𝕜` -/
namespace fourier

variables {𝕜 : Type*} [comm_ring 𝕜] [measurable_space 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]

section defs

variables [complete_space E]

/-- The Fourier transform integral for `f : 𝕜 → E`, with respect to the measure `μ` and additive
character `e`. -/
def fourier_integral
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E :=
vector_fourier.fourier_integral e μ (linear_map.mul 𝕜 𝕜) f w

lemma fourier_integral_def (e : (multiplicative 𝕜) →* 𝕊) (μ : measure 𝕜) (f : 𝕜 → E) (w : 𝕜) :
  fourier_integral e μ f w = ∫ (v : 𝕜), e[-(v * w)] • f v ∂μ :=
rfl

lemma fourier_integral_smul_const
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure 𝕜) (f : 𝕜 → E) (r : ℂ) :
  fourier_integral e μ (r • f) = r • (fourier_integral e μ f) :=
vector_fourier.fourier_integral_smul_const _ _ _ _ _

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
lemma fourier_integral_norm_le (e : (multiplicative 𝕜) →* 𝕊) {μ : measure 𝕜}
  {f : 𝕜 → E} (hf : integrable f μ) (w : 𝕜) :
  ‖fourier_integral e μ f w‖ ≤ ‖hf.to_L1 f‖ :=
vector_fourier.fourier_integral_norm_le _ _ _ _

/-- The Fourier transform converts right-translation into scalar multiplication by a phase factor.-/
lemma fourier_integral_comp_add_right [has_measurable_add 𝕜]
  (e : (multiplicative 𝕜) →* 𝕊) (μ : measure 𝕜) [μ.is_add_right_invariant] (f : 𝕜 → E) (v₀ : 𝕜) :
  fourier_integral e μ (f ∘ (λ v, v + v₀)) = λ w, e [v₀ * w] • fourier_integral e μ f w :=
vector_fourier.fourier_integral_comp_add_right _ _ _ _ _

end defs

end fourier

open_locale real

namespace real

/-- The standard additive character of `ℝ`, given by `λ x, exp (2 * π * x * I)`. -/
def fourier_char : (multiplicative ℝ) →* 𝕊 :=
{ to_fun := λ z, exp_map_circle (2 * π * z.to_add),
  map_one' := by rw [to_add_one, mul_zero, exp_map_circle_zero],
  map_mul' := λ x y, by rw [to_add_mul, mul_add, exp_map_circle_add] }

lemma fourier_char_apply (x : ℝ) :
  real.fourier_char [x] = complex.exp (↑(2 * π * x) * complex.I) :=
by refl

@[continuity]
lemma continuous_fourier_char : continuous real.fourier_char :=
(map_continuous exp_map_circle).comp (continuous_const.mul continuous_to_add)

variables {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]

lemma vector_fourier_integral_eq_integral_exp_smul
  {V : Type*} [add_comm_group V] [module ℝ V] [measurable_space V]
  {W : Type*} [add_comm_group W] [module ℝ W]
  (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : measure V) (f : V → E) (w : W) :
  vector_fourier.fourier_integral fourier_char μ L f w
  = ∫ (v : V), complex.exp (↑(-2 * π * L v w) * complex.I) • f v ∂μ :=
by simp_rw [vector_fourier.fourier_integral, real.fourier_char_apply, mul_neg, neg_mul]

/-- The Fourier integral for `f : ℝ → E`, with respect to the standard additive character and
measure on `ℝ`. -/
def fourier_integral (f : ℝ → E) (w : ℝ) := fourier.fourier_integral fourier_char volume f w

lemma fourier_integral_def (f : ℝ → E) (w : ℝ) :
  fourier_integral f w = ∫ (v : ℝ), fourier_char [-(v * w)] • f v :=
rfl

localized "notation (name := fourier_integral) `𝓕` := real.fourier_integral" in fourier_transform

lemma fourier_integral_eq_integral_exp_smul
  {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]
  (f : ℝ → E) (w : ℝ) :
  𝓕 f w = ∫ (v : ℝ), complex.exp (↑(-2 * π * v * w) * complex.I) • f v :=
by simp_rw [fourier_integral_def, real.fourier_char_apply, mul_neg, neg_mul, mul_assoc]

end real
