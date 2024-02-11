/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.continuous_function.bounded
import topology.algebra.module.weak_dual
import measure_theory.integral.bochner

/-!
# Finite measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the type of finite measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of finite measures is equipped with the topology of weak convergence
of measures. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

## Main definitions

The main definitions are
 * the type `measure_theory.finite_measure Ω` with the topology of weak convergence;
 * `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `Ω` via integration:
   `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
 * `measure_theory.finite_measure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
   measures is characterized by the convergence of integrals of all bounded continuous functions.
   This shows that the chosen definition of topology coincides with the common textbook definition
   of weak convergence of measures. A similar characterization by the convergence of integrals (in
   the `measure_theory.lintegral` sense) of all bounded continuous nonnegative functions is
   `measure_theory.finite_measure.tendsto_iff_forall_lintegral_tendsto`.

## Implementation notes

The topology of weak convergence of finite Borel measures is defined using a mapping from
`measure_theory.finite_measure Ω` to `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The implementation of `measure_theory.finite_measure Ω` and is directly as a subtype of
`measure_theory.measure Ω`, and the coercion to a function is the composition `ennreal.to_nnreal`
and the coercion to function of `measure_theory.measure Ω`. Another alternative would have been to
use a bijection with `measure_theory.vector_measure Ω ℝ≥0` as an intermediate step. Some
considerations:
 * Potential advantages of using the `nnreal`-valued vector measure alternative:
   * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
     `nnreal`-valued API could be more directly available.
 * Potential drawbacks of the vector measure alternative:
   * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
     have measure 0.
   * No integration theory directly. E.g., the topology definition requires
     `measure_theory.lintegral` w.r.t. a coercion to `measure_theory.measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure

-/

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topology ennreal nnreal bounded_continuous_function

namespace measure_theory

namespace finite_measure

section finite_measure
/-! ### Finite measures

In this section we define the `Type` of `finite_measure Ω`, when `Ω` is a measurable space. Finite
measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space Ω]`), then `finite_measure Ω` is equipped with the topology
of weak convergence of measures. This is implemented by defining a pairing of finite measures `μ`
on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration, and using the
associated weak topology (essentially the weak-star topology on the dual of `Ω →ᵇ ℝ≥0`).
-/

variables {Ω : Type*} [measurable_space Ω]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def _root_.measure_theory.finite_measure (Ω : Type*) [measurable_space Ω] : Type* :=
{μ : measure Ω // is_finite_measure μ}

/-- A finite measure can be interpreted as a measure. -/
instance : has_coe (finite_measure Ω) (measure_theory.measure Ω) := coe_subtype

instance is_finite_measure (μ : finite_measure Ω) :
  is_finite_measure (μ : measure Ω) := μ.prop

instance : has_coe_to_fun (finite_measure Ω) (λ _, set Ω → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : finite_measure Ω) :
  (ν : set Ω → ℝ≥0) = λ s, ((ν : measure Ω) s).to_nnreal := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : finite_measure Ω) (s : set Ω) :
  (ν s : ℝ≥0∞) = (ν : measure Ω) s := ennreal.coe_to_nnreal (measure_lt_top ↑ν s).ne

@[simp] lemma val_eq_to_measure (ν : finite_measure Ω) : ν.val = (ν : measure Ω) := rfl

lemma coe_injective : function.injective (coe : finite_measure Ω → measure Ω) :=
subtype.coe_injective

lemma apply_mono (μ : finite_measure Ω) {s₁ s₂ : set Ω} (h : s₁ ⊆ s₂) :
  μ s₁ ≤ μ s₂ :=
begin
  change ((μ : measure Ω) s₁).to_nnreal ≤ ((μ : measure Ω) s₂).to_nnreal,
  have key : (μ : measure Ω) s₁ ≤ (μ : measure Ω) s₂ := (μ : measure Ω).mono h,
  apply (ennreal.to_nnreal_le_to_nnreal (measure_ne_top _ s₁) (measure_ne_top _ s₂)).mpr key,
end

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure Ω) univ`. -/
def mass (μ : finite_measure Ω) : ℝ≥0 := μ univ

@[simp] lemma ennreal_mass {μ : finite_measure Ω} :
  (μ.mass : ℝ≥0∞) = (μ : measure Ω) univ := ennreal_coe_fn_eq_coe_fn_to_measure μ set.univ

instance has_zero : has_zero (finite_measure Ω) :=
{ zero := ⟨0, measure_theory.is_finite_measure_zero⟩ }

@[simp] lemma zero.mass : (0 : finite_measure Ω).mass = 0 := rfl

@[simp] lemma mass_zero_iff (μ : finite_measure Ω) : μ.mass = 0 ↔ μ = 0 :=
begin
  refine ⟨λ μ_mass, _, (λ hμ, by simp only [hμ, zero.mass])⟩,
  ext1,
  apply measure.measure_univ_eq_zero.mp,
  rwa [← ennreal_mass, ennreal.coe_eq_zero],
end

lemma mass_nonzero_iff (μ : finite_measure Ω) : μ.mass ≠ 0 ↔ μ ≠ 0 :=
begin
  rw not_iff_not,
  exact finite_measure.mass_zero_iff μ,
end

@[ext] lemma eq_of_forall_measure_apply_eq (μ ν : finite_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → (μ : measure Ω) s = (ν : measure Ω) s) :
  μ = ν :=
by { ext1, ext1 s s_mble, exact h s s_mble, }

lemma eq_of_forall_apply_eq (μ ν : finite_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

instance : inhabited (finite_measure Ω) := ⟨0⟩

instance : has_add (finite_measure Ω) :=
{ add := λ μ ν, ⟨μ + ν, measure_theory.is_finite_measure_add⟩ }

variables {R : Type*} [has_smul R ℝ≥0] [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0 ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]

instance : has_smul R (finite_measure Ω) :=
{ smul := λ (c : R) μ, ⟨c • μ, measure_theory.is_finite_measure_smul_of_nnreal_tower⟩, }

@[simp, norm_cast] lemma coe_zero : (coe : finite_measure Ω → measure Ω) 0 = 0 := rfl

@[simp, norm_cast] lemma coe_add (μ ν : finite_measure Ω) : ↑(μ + ν) = (↑μ + ↑ν : measure Ω) := rfl

@[simp, norm_cast] lemma coe_smul (c : R) (μ : finite_measure Ω) :
  ↑(c • μ) = (c • ↑μ : measure Ω) := rfl

@[simp, norm_cast] lemma coe_fn_zero :
  (⇑(0 : finite_measure Ω) : set Ω → ℝ≥0) = (0 : set Ω → ℝ≥0) := by { funext, refl, }

@[simp, norm_cast] lemma coe_fn_add (μ ν : finite_measure Ω) :
  (⇑(μ + ν) : set Ω → ℝ≥0) = (⇑μ + ⇑ν : set Ω → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe], }

@[simp, norm_cast] lemma coe_fn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] (c : R) (μ : finite_measure Ω) :
  (⇑(c • μ) : set Ω → ℝ≥0) = c • (⇑μ : set Ω → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe, ennreal.coe_smul], }

instance : add_comm_monoid (finite_measure Ω) :=
coe_injective.add_comm_monoid coe coe_zero coe_add (λ _ _, coe_smul _ _)

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure Ω →+ measure Ω :=
{ to_fun := coe, map_zero' := coe_zero, map_add' := coe_add }

instance {Ω : Type*} [measurable_space Ω] : module ℝ≥0 (finite_measure Ω) :=
function.injective.module _ coe_add_monoid_hom coe_injective coe_smul

@[simp] lemma coe_fn_smul_apply [is_scalar_tower R ℝ≥0 ℝ≥0]
  (c : R) (μ : finite_measure Ω) (s : set Ω) :
  (c • μ) s  = c • (μ s) :=
by { simp only [coe_fn_smul, pi.smul_apply], }

/-- Restrict a finite measure μ to a set A. -/
def restrict (μ : finite_measure Ω) (A : set Ω) : finite_measure Ω :=
{ val := (μ : measure Ω).restrict A,
  property := measure_theory.is_finite_measure_restrict μ A, }

lemma restrict_measure_eq (μ : finite_measure Ω) (A : set Ω) :
  (μ.restrict A : measure Ω) = (μ : measure Ω).restrict A := rfl

lemma restrict_apply_measure (μ : finite_measure Ω) (A : set Ω)
  {s : set Ω} (s_mble : measurable_set s) :
  (μ.restrict A : measure Ω) s = (μ : measure Ω) (s ∩ A) :=
measure.restrict_apply s_mble

lemma restrict_apply (μ : finite_measure Ω) (A : set Ω)
  {s : set Ω} (s_mble : measurable_set s) :
  (μ.restrict A) s = μ (s ∩ A) :=
begin
  apply congr_arg ennreal.to_nnreal,
  exact measure.restrict_apply s_mble,
end

lemma restrict_mass (μ : finite_measure Ω) (A : set Ω) :
  (μ.restrict A).mass = μ A :=
by simp only [mass, restrict_apply μ A measurable_set.univ, univ_inter]

lemma restrict_eq_zero_iff (μ : finite_measure Ω) (A : set Ω) :
  μ.restrict A = 0 ↔ μ A = 0 :=
by rw [← mass_zero_iff, restrict_mass]

lemma restrict_nonzero_iff (μ : finite_measure Ω) (A : set Ω) :
  μ.restrict A ≠ 0 ↔ μ A ≠ 0 :=
by rw [← mass_nonzero_iff, restrict_mass]

variables [topological_space Ω]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def test_against_nn (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) : ℝ≥0 :=
(∫⁻ ω, f ω ∂(μ : measure Ω)).to_nnreal

lemma _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {Ω : Type*}
  [topological_space Ω] [measurable_space Ω] [opens_measurable_space Ω] (f : Ω →ᵇ ℝ≥0) :
  measurable (λ ω, (f ω : ℝ≥0∞)) :=
measurable_coe_nnreal_ennreal.comp f.continuous.measurable

lemma _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ≥0) :
  ∫⁻ ω, f ω ∂μ < ∞ :=
begin
  apply is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal,
  use nndist f 0,
  intros x,
  have key := bounded_continuous_function.nnreal.upper_bound f x,
  rw ennreal.coe_le_coe,
  have eq : nndist f 0 = ⟨dist f 0, dist_nonneg⟩,
  { ext,
    simp only [real.coe_to_nnreal', max_eq_left_iff, subtype.coe_mk, coe_nndist], },
  rwa eq at key,
end

@[simp] lemma test_against_nn_coe_eq {μ : finite_measure Ω} {f : Ω →ᵇ ℝ≥0} :
  (μ.test_against_nn f : ℝ≥0∞) = ∫⁻ ω, f ω ∂(μ : measure Ω) :=
ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal _ f).ne

lemma test_against_nn_const (μ : finite_measure Ω) (c : ℝ≥0) :
  μ.test_against_nn (bounded_continuous_function.const Ω c) = c * μ.mass :=
by simp [← ennreal.coe_eq_coe]

lemma test_against_nn_mono (μ : finite_measure Ω)
  {f g : Ω →ᵇ ℝ≥0} (f_le_g : (f : Ω → ℝ≥0) ≤ g) :
  μ.test_against_nn f ≤ μ.test_against_nn g :=
begin
  simp only [←ennreal.coe_le_coe, test_against_nn_coe_eq],
  exact lintegral_mono (λ ω, ennreal.coe_mono (f_le_g ω)),
end

@[simp] lemma test_against_nn_zero (μ : finite_measure Ω) : μ.test_against_nn 0 = 0 :=
by simpa only [zero_mul] using μ.test_against_nn_const 0

@[simp] lemma test_against_nn_one (μ : finite_measure Ω) : μ.test_against_nn 1 = μ.mass :=
begin
  simp only [test_against_nn, coe_one, pi.one_apply, ennreal.coe_one, lintegral_one],
  refl,
end

@[simp] lemma zero.test_against_nn_apply (f : Ω →ᵇ ℝ≥0) :
  (0 : finite_measure Ω).test_against_nn f = 0 :=
by simp only [test_against_nn, coe_zero, lintegral_zero_measure, ennreal.zero_to_nnreal]

lemma zero.test_against_nn : (0 : finite_measure Ω).test_against_nn = 0 :=
by { funext, simp only [zero.test_against_nn_apply, pi.zero_apply], }

@[simp] lemma smul_test_against_nn_apply (c : ℝ≥0) (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  (c • μ).test_against_nn f  = c • (μ.test_against_nn f) :=
by simp only [test_against_nn, coe_smul, smul_eq_mul, ← ennreal.smul_to_nnreal,
  ennreal.smul_def, lintegral_smul_measure]

variables [opens_measurable_space Ω]

lemma test_against_nn_add (μ : finite_measure Ω) (f₁ f₂ : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn (f₁ + f₂) = μ.test_against_nn f₁ + μ.test_against_nn f₂ :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_add, ennreal.coe_add,
             pi.add_apply, test_against_nn_coe_eq],
  exact lintegral_add_left (bounded_continuous_function.nnreal.to_ennreal_comp_measurable _) _
end

lemma test_against_nn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] [pseudo_metric_space R] [has_zero R]
  [has_bounded_smul R ℝ≥0]
  (μ : finite_measure Ω) (c : R) (f : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn (c • f) = c • μ.test_against_nn f :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_smul,
             test_against_nn_coe_eq, ennreal.coe_smul],
  simp_rw [←smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ←smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞),
           smul_eq_mul],
  exact @lintegral_const_mul _ _ (μ : measure Ω) (c • 1)  _
                   (bounded_continuous_function.nnreal.to_ennreal_comp_measurable f),
end

lemma test_against_nn_lipschitz_estimate (μ : finite_measure Ω) (f g : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn f ≤ μ.test_against_nn g + (nndist f g) * μ.mass :=
begin
  simp only [←μ.test_against_nn_const (nndist f g), ←test_against_nn_add, ←ennreal.coe_le_coe,
             bounded_continuous_function.coe_add, const_apply, ennreal.coe_add, pi.add_apply,
             coe_nnreal_ennreal_nndist, test_against_nn_coe_eq],
  apply lintegral_mono,
  have le_dist : ∀ ω, dist (f ω) (g ω) ≤ nndist f g :=
  bounded_continuous_function.dist_coe_le_dist,
  intros ω,
  have le' : f ω ≤ g ω + nndist f g,
  { apply (nnreal.le_add_nndist (f ω) (g ω)).trans,
    rw add_le_add_iff_left,
    exact dist_le_coe.mp (le_dist ω), },
  have le : (f ω : ℝ≥0∞) ≤ (g ω : ℝ≥0∞) + (nndist f g),
  by { rw ←ennreal.coe_add, exact ennreal.coe_mono le', },
  rwa [coe_nnreal_ennreal_nndist] at le,
end

lemma test_against_nn_lipschitz (μ : finite_measure Ω) :
  lipschitz_with μ.mass (λ (f : Ω →ᵇ ℝ≥0), μ.test_against_nn f) :=
begin
  rw lipschitz_with_iff_dist_le_mul,
  intros f₁ f₂,
  suffices : abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * (dist f₁ f₂),
  { rwa nnreal.dist_eq, },
  apply abs_le.mpr,
  split,
  { have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul, nndist_comm] at key, },
  { have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul] at key, },
end

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bcnn (μ : finite_measure Ω) :
  weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
{ to_fun := λ f, μ.test_against_nn f,
  map_add' := test_against_nn_add μ,
  map_smul' := test_against_nn_smul μ,
  cont := μ.test_against_nn_lipschitz.continuous, }

@[simp] lemma coe_to_weak_dual_bcnn (μ : finite_measure Ω) :
  ⇑μ.to_weak_dual_bcnn = μ.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ x, f x ∂(μ : measure Ω)).to_nnreal := rfl

/-- The topology of weak convergence on `measure_theory.finite_measure Ω` is inherited (induced)
from the weak-* topology on `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)` via the function
`measure_theory.finite_measure.to_weak_dual_bcnn`. -/
instance : topological_space (finite_measure Ω) :=
topological_space.induced to_weak_dual_bcnn infer_instance

lemma to_weak_dual_bcnn_continuous :
  continuous (@to_weak_dual_bcnn Ω _ _ _) :=
continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : Ω →ᵇ ℝ≥0) :
  continuous (λ (μ : finite_measure Ω), μ.test_against_nn f) :=
(by apply (weak_bilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
  continuous ((λ φ : weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0), φ f) ∘ to_weak_dual_bcnn))

/-- The total mass of a finite measure depends continuously on the measure. -/
lemma continuous_mass : continuous (λ (μ : finite_measure Ω), μ.mass) :=
by { simp_rw ←test_against_nn_one, exact continuous_test_against_nn_eval 1, }

/-- Convergence of finite measures implies the convergence of their total masses. -/
lemma _root_.filter.tendsto.mass {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} (h : tendsto μs F (𝓝 μ)) :
  tendsto (λ i, (μs i).mass) F (𝓝 μ.mass) :=
(continuous_mass.tendsto μ).comp h

lemma tendsto_iff_weak_star_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔ tendsto (λ i, (μs(i)).to_weak_dual_bcnn) F (𝓝 μ.to_weak_dual_bcnn) :=
inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_to_weak_dual_bcnn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (μs i).to_weak_dual_bcnn f) F (𝓝 (μ.to_weak_dual_bcnn f)) :=
by { rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing], refl, }

theorem tendsto_iff_forall_test_against_nn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (μs i).test_against_nn f) F (𝓝 (μ.test_against_nn f)) :=
by { rw finite_measure.tendsto_iff_forall_to_weak_dual_bcnn_tendsto, refl, }

/-- If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `finite_measure.tendsto_zero_of_tendsto_zero_mass` for
a formulation stating the weak convergence of measures. -/
lemma tendsto_zero_test_against_nn_of_tendsto_zero_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) (f : Ω →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).test_against_nn f) F (𝓝 0) :=
begin
  apply tendsto_iff_dist_tendsto_zero.mpr,
  have obs := λ i, (μs i).test_against_nn_lipschitz_estimate f 0,
  simp_rw [test_against_nn_zero, zero_add] at obs,
  simp_rw (show ∀ i, dist ((μs i).test_against_nn f) 0 = (μs i).test_against_nn f,
    by simp only [dist_nndist, nnreal.nndist_zero_eq_val', eq_self_iff_true,
                  implies_true_iff]),
  refine squeeze_zero (λ i, nnreal.coe_nonneg _) obs _,
  simp_rw nnreal.coe_mul,
  have lim_pair : tendsto (λ i, (⟨nndist f 0, (μs i).mass⟩ : ℝ × ℝ)) F (𝓝 (⟨nndist f 0, 0⟩)),
  { refine (prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, _⟩,
    exact (nnreal.continuous_coe.tendsto 0).comp mass_lim, },
  have key := tendsto_mul.comp lim_pair,
  rwa mul_zero at key,
end

/-- If the total masses of finite measures tend to zero, then the measures tend to zero. -/
lemma tendsto_zero_of_tendsto_zero_mass {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) :
  tendsto μs F (𝓝 0) :=
begin
  rw tendsto_iff_forall_test_against_nn_tendsto,
  intro f,
  convert tendsto_zero_test_against_nn_of_tendsto_zero_mass mass_lim f,
  rw [zero.test_against_nn_apply],
end

/-- A characterization of weak convergence in terms of integrals of bounded continuous
nonnegative functions. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0),
    tendsto (λ i, (∫⁻ x, (f x) ∂(μs(i) : measure Ω))) F (𝓝 ((∫⁻ x, (f x) ∂(μ : measure Ω)))) :=
begin
  rw tendsto_iff_forall_to_weak_dual_bcnn_tendsto,
  simp_rw [to_weak_dual_bcnn_apply _ _, ←test_against_nn_coe_eq,
           ennreal.tendsto_coe, ennreal.to_nnreal_coe],
end

end finite_measure -- section

section finite_measure_bounded_convergence
/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/

variables {Ω : Type*} [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `measure_theory.lintegral`, i.e., the functions and their integrals are
   `ℝ≥0∞`-valued.
-/
lemma tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : filter ι} [L.is_countably_generated]
  (μ : measure Ω) [is_finite_measure μ] {fs : ι → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
  (fs_lim : ∀ᵐ (ω : Ω) ∂μ, tendsto (λ i, fs i ω) L (𝓝 (f ω))) :
  tendsto (λ i, (∫⁻ ω, fs i ω ∂μ)) L (𝓝 (∫⁻ ω, (f ω) ∂μ)) :=
begin
  simpa only using tendsto_lintegral_filter_of_dominated_convergence (λ _, c)
    (eventually_of_forall ((λ i, (ennreal.continuous_coe.comp (fs i).continuous).measurable)))
    _ ((@lintegral_const_lt_top _ _ μ _ _ (@ennreal.coe_ne_top c)).ne) _,
  { simpa only [ennreal.coe_le_coe] using fs_le_const, },
  { simpa only [ennreal.tendsto_coe] using fs_lim, },
end

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`measure_theory.lintegral`) against the finite
measure tend to the integral of the limit.

A related result with more general assumptions is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
lemma tendsto_lintegral_nn_of_le_const (μ : finite_measure Ω) {fs : ℕ → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω → ℝ≥0}
  (fs_lim : ∀ ω, tendsto (λ n, fs n ω) at_top (𝓝 (f ω))) :
  tendsto (λ n, (∫⁻ ω, fs n ω ∂(μ : measure Ω))) at_top (𝓝 (∫⁻ ω, (f ω) ∂(μ : measure Ω))) :=
tendsto_lintegral_nn_filter_of_le_const μ
  (eventually_of_forall (λ n, eventually_of_forall (fs_le_const n))) (eventually_of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is the pairing against non-negative continuous test functions
   (`measure_theory.finite_measure.test_against_nn`).

A related result using `measure_theory.lintegral` for integration is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
lemma tendsto_test_against_nn_filter_of_le_const {ι : Type*} {L : filter ι}
  [L.is_countably_generated] {μ : finite_measure Ω} {fs : ι → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂(μ : measure Ω), fs i ω ≤ c) {f : Ω →ᵇ ℝ≥0}
  (fs_lim : ∀ᵐ (ω : Ω) ∂(μ : measure Ω), tendsto (λ i, fs i ω) L (𝓝 (f ω))) :
  tendsto (λ i, μ.test_against_nn (fs i)) L (𝓝 (μ.test_against_nn f)) :=
begin
  apply (ennreal.tendsto_to_nnreal
         (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f).ne).comp,
  exact tendsto_lintegral_nn_filter_of_le_const μ fs_le_const fs_lim,
end

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant and
tend pointwise to a limit, then their integrals (`measure_theory.finite_measure.test_against_nn`)
against the finite measure tend to the integral of the limit.

Related results:
 * `measure_theory.finite_measure.tendsto_test_against_nn_filter_of_le_const`:
   more general assumptions
 * `measure_theory.finite_measure.tendsto_lintegral_nn_of_le_const`:
   using `measure_theory.lintegral` for integration.
-/
lemma tendsto_test_against_nn_of_le_const {μ : finite_measure Ω}
  {fs : ℕ → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0} (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω →ᵇ ℝ≥0}
  (fs_lim : ∀ ω, tendsto (λ n, fs n ω) at_top (𝓝 (f ω))) :
  tendsto (λ n, μ.test_against_nn (fs n)) at_top (𝓝 (μ.test_against_nn f)) :=
tendsto_test_against_nn_filter_of_le_const
  (eventually_of_forall (λ n, eventually_of_forall (fs_le_const n))) (eventually_of_forall fs_lim)

end finite_measure_bounded_convergence -- section

section finite_measure_convergence_by_bounded_continuous_functions
/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/

variables {Ω : Type*} [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω]

lemma integrable_of_bounded_continuous_to_nnreal
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ≥0) :
  integrable ((coe : ℝ≥0 → ℝ) ∘ ⇑f) μ :=
begin
  refine ⟨(nnreal.continuous_coe.comp f.continuous).measurable.ae_strongly_measurable, _⟩,
  simp only [has_finite_integral, nnreal.nnnorm_eq],
  exact lintegral_lt_top_of_bounded_continuous_to_nnreal _ f,
end

lemma integrable_of_bounded_continuous_to_real
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ) :
  integrable ⇑f μ :=
begin
  refine ⟨f.continuous.measurable.ae_strongly_measurable, _⟩,
  have aux : (coe : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = (λ x, ‖f x‖),
  { ext ω,
    simp only [function.comp_app, bounded_continuous_function.nnnorm_coe_fun_eq, coe_nnnorm], },
  apply (has_finite_integral_iff_norm ⇑f).mpr,
  rw ← of_real_integral_eq_lintegral_of_real,
  { exact ennreal.of_real_lt_top, },
  { exact aux ▸ integrable_of_bounded_continuous_to_nnreal μ f.nnnorm, },
  { exact eventually_of_forall (λ ω, norm_nonneg (f ω)), },
end

lemma _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ) :
  ∫ ω, f ω ∂μ = ∫ ω, f.nnreal_part ω ∂μ - ∫ ω, (-f).nnreal_part ω ∂μ :=
by simp only [f.self_eq_nnreal_part_sub_nnreal_part_neg,
              pi.sub_apply, integral_sub, integrable_of_bounded_continuous_to_nnreal]

lemma lintegral_lt_top_of_bounded_continuous_to_real
  {Ω : Type*} [measurable_space Ω] [topological_space Ω] (μ : measure Ω) [is_finite_measure μ]
  (f : Ω →ᵇ ℝ) :
  ∫⁻ ω, ennreal.of_real (f ω) ∂μ < ∞ :=
lintegral_lt_top_of_bounded_continuous_to_nnreal _ f.nnreal_part

theorem tendsto_of_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω}
  (h : (∀ (f : Ω →ᵇ ℝ),
       tendsto (λ i, (∫ x, (f x) ∂(μs i : measure Ω))) F (𝓝 ((∫ x, (f x) ∂(μ : measure Ω)))))) :
  tendsto μs F (𝓝 μ) :=
begin
  apply (@tendsto_iff_forall_lintegral_tendsto Ω _ _ _ γ F μs μ).mpr,
  intro f,
  have key := @ennreal.tendsto_to_real_iff _ F
              _ (λ i, (lintegral_lt_top_of_bounded_continuous_to_nnreal (μs i : measure Ω) f).ne)
              _ (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f).ne,
  simp only [ennreal.of_real_coe_nnreal] at key,
  apply key.mp,
  have lip : lipschitz_with 1 (coe : ℝ≥0 → ℝ), from isometry_subtype_coe.lipschitz,
  set f₀ := bounded_continuous_function.comp _ lip f with def_f₀,
  have f₀_eq : ⇑f₀ = (coe : ℝ≥0 → ℝ) ∘ ⇑f, by refl,
  have f₀_nn : 0 ≤ ⇑f₀, from λ _, by simp only [f₀_eq, pi.zero_apply, nnreal.zero_le_coe],
  have f₀_ae_nn : 0 ≤ᵐ[(μ : measure Ω)] ⇑f₀, from eventually_of_forall f₀_nn,
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : measure Ω)] ⇑f₀, from λ i, eventually_of_forall f₀_nn,
  have aux := integral_eq_lintegral_of_nonneg_ae f₀_ae_nn
              f₀.continuous.measurable.ae_strongly_measurable,
  have auxs := λ i, integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i)
              f₀.continuous.measurable.ae_strongly_measurable,
  simp only [f₀_eq, ennreal.of_real_coe_nnreal] at aux auxs,
  simpa only [←aux, ←auxs] using h f₀,
end

lemma _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral
  (f : Ω →ᵇ ℝ≥0) (μ : measure Ω) :
  (∫⁻ x, (f x : ℝ≥0∞) ∂μ).to_real = (∫ x, f x ∂μ) :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _
     (nnreal.continuous_coe.comp f.continuous).measurable.ae_strongly_measurable,
  { simp only [ennreal.of_real_coe_nnreal], },
  { apply eventually_of_forall,
    simp only [pi.zero_apply, nnreal.zero_le_coe, implies_true_iff], },
end

/-- A characterization of weak convergence in terms of integrals of bounded continuous
real-valued functions. -/
theorem tendsto_iff_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ),
    tendsto (λ i, (∫ x, (f x) ∂(μs i : measure Ω))) F (𝓝 ((∫ x, (f x) ∂(μ : measure Ω)))) :=
begin
  refine ⟨_, tendsto_of_forall_integral_tendsto⟩,
  rw tendsto_iff_forall_lintegral_tendsto,
  intros h f,
  simp_rw bounded_continuous_function.integral_eq_integral_nnreal_part_sub,
  set f_pos := f.nnreal_part with def_f_pos,
  set f_neg := (-f).nnreal_part with def_f_neg,
  have tends_pos := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f_pos).ne)).comp (h f_pos),
  have tends_neg := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f_neg).ne)).comp (h f_neg),
  have aux : ∀ (g : Ω →ᵇ ℝ≥0), ennreal.to_real ∘ (λ (i : γ), ∫⁻ (x : Ω), ↑(g x) ∂(μs i : measure Ω))
         = λ (i : γ), (∫⁻ (x : Ω), ↑(g x) ∂(μs i : measure Ω)).to_real, from λ _, rfl,
  simp_rw [aux, bounded_continuous_function.nnreal.to_real_lintegral_eq_integral]
          at tends_pos tends_neg,
  exact tendsto.sub tends_pos tends_neg,
end

end finite_measure_convergence_by_bounded_continuous_functions -- section

end finite_measure -- namespace

end measure_theory -- namespace
