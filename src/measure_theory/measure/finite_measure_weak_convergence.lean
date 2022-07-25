/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.measure.measure_space
import measure_theory.integral.set_integral
import measure_theory.integral.average
import topology.continuous_function.bounded
import topology.algebra.module.weak_dual
import topology.metric_space.thickened_indicator

/-!
# Weak convergence of (finite) measures

This file defines the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

TODOs:
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the
 * types `measure_theory.finite_measure α` and `measure_theory.probability_measure α` with
   the topologies of weak convergence;
 * `measure_theory.finite_measure.normalize`, normalizing a finite measure to a probability measure
   (returns junk for the zero measure);
 * `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `α`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `α` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `α` via integration:
   `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`
 * `measure_theory.finite_measure.tendsto_iff_forall_integral_tendsto` and
   `measure_theory.probability_measure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
   measures and probability measures is characterized by the convergence of integrals of all
   bounded continuous functions. This shows that the given definition of topology corresponds to
   the common textbook definition of weak convergence of measures.
   Similar characterizations by the convergence of integrals (in the `measure_theory.lintegral`
   sense) of all bounded continuous nonnegative functions are
   `measure_theory.finite_measure.tendsto_iff_forall_lintegral_tendsto` and
   `measure_theory.probability_measure.tendsto_iff_forall_lintegral_tendsto`.
 * `measure_theory.finite_measure.tendsto_normalize_iff_tendsto`: The convergence of finite
   measures to a nonzero limit is characterized by the convergence of the probability-normalized
   versions and of the total masses.

TODO:
* Portmanteau theorem:
  * `measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto` proves one implication.
    The current formulation assumes `pseudo_emetric_space`. The only reason is to have
    bounded continuous pointwise approximations to the indicator function of a closed set. Clearly
    for example metrizability or pseudo-emetrizability would be sufficient assumptions. The
    typeclass assumptions should be later adjusted in a way that takes into account use cases, but
    the proof will presumably remain essentially the same.
  * Prove the rest of the implications.

## Notations

No new notation is introduced.

## Implementation notes

The topology of weak convergence of finite Borel measures will be defined using a mapping from
`measure_theory.finite_measure α` to `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The current implementation of `measure_theory.finite_measure α` and
`measure_theory.probability_measure α` is directly as subtypes of `measure_theory.measure α`, and
the coercion to a function is the composition `ennreal.to_nnreal` and the coercion to function
of `measure_theory.measure α`. Another alternative would be to use a bijection
with `measure_theory.vector_measure α ℝ≥0` as an intermediate step. The choice of implementation
should not have drastic downstream effects, so it can be changed later if appropriate.

Potential advantages of using the `nnreal`-valued vector measure alternative:
 * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
   `nnreal`-valued API could be more directly available.

Potential drawbacks of the vector measure alternative:
 * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
   have measure 0.
 * No integration theory directly. E.g., the topology definition requires
   `measure_theory.lintegral` w.r.t. a coercion to `measure_theory.measure α` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure, probability measure

-/

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topological_space ennreal nnreal bounded_continuous_function

namespace measure_theory

namespace finite_measure

section finite_measure
/-! ### Finite measures

In this section we define the `Type` of `finite_measure α`, when `α` is a measurable space. Finite
measures on `α` are a module over `ℝ≥0`.

If `α` is moreover a topological space and the sigma algebra on `α` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space α]`), then `finite_measure α` is equipped with the topology
of weak convergence of measures. This is implemented by defining a pairing of finite measures `μ`
on `α` with continuous bounded nonnegative functions `f : α →ᵇ ℝ≥0` via integration, and using the
associated weak topology (essentially the weak-star topology on the dual of `α →ᵇ ℝ≥0`).
-/

variables {α : Type*} [measurable_space α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def _root_.measure_theory.finite_measure (α : Type*) [measurable_space α] : Type* :=
{μ : measure α // is_finite_measure μ}

/-- A finite measure can be interpreted as a measure. -/
instance : has_coe (finite_measure α) (measure_theory.measure α) := coe_subtype

instance is_finite_measure (μ : finite_measure α) :
  is_finite_measure (μ : measure α) := μ.prop

instance : has_coe_to_fun (finite_measure α) (λ _, set α → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : finite_measure α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : finite_measure α) (s : set α) :
  (ν s : ℝ≥0∞) = (ν : measure α) s := ennreal.coe_to_nnreal (measure_lt_top ↑ν s).ne

@[simp] lemma val_eq_to_measure (ν : finite_measure α) : ν.val = (ν : measure α) := rfl

lemma coe_injective : function.injective (coe : finite_measure α → measure α) :=
subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : finite_measure α) : ℝ≥0 := μ univ

@[simp] lemma ennreal_mass {μ : finite_measure α} :
  (μ.mass : ℝ≥0∞) = (μ : measure α) univ := ennreal_coe_fn_eq_coe_fn_to_measure μ set.univ

instance has_zero : has_zero (finite_measure α) :=
{ zero := ⟨0, measure_theory.is_finite_measure_zero⟩ }

@[simp] lemma zero.mass : (0 : finite_measure α).mass = 0 := rfl

@[simp] lemma mass_zero_iff (μ : finite_measure α) : μ.mass = 0 ↔ μ = 0 :=
begin
  refine ⟨λ μ_mass, _, (λ hμ, by simp only [hμ, zero.mass])⟩,
  ext1,
  apply measure.measure_univ_eq_zero.mp,
  rwa [← ennreal_mass, ennreal.coe_eq_zero],
end

lemma mass_nonzero_iff (μ : finite_measure α) : μ.mass ≠ 0 ↔ μ ≠ 0 :=
begin
  rw not_iff_not,
  exact finite_measure.mass_zero_iff μ,
end

@[ext] lemma extensionality (μ ν : finite_measure α)
  (h : ∀ (s : set α), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1, ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

instance : inhabited (finite_measure α) := ⟨0⟩

instance : has_add (finite_measure α) :=
{ add := λ μ ν, ⟨μ + ν, measure_theory.is_finite_measure_add⟩ }

variables {R : Type*} [has_smul R ℝ≥0] [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0 ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]

instance : has_smul R (finite_measure α) :=
{ smul := λ (c : R) μ, ⟨c • μ, measure_theory.is_finite_measure_smul_of_nnreal_tower⟩, }

@[simp, norm_cast] lemma coe_zero : (coe : finite_measure α → measure α) 0 = 0 := rfl

@[simp, norm_cast] lemma coe_add (μ ν : finite_measure α) : ↑(μ + ν) = (↑μ + ↑ν : measure α) := rfl

@[simp, norm_cast] lemma coe_smul (c : R) (μ : finite_measure α) :
  ↑(c • μ) = (c • ↑μ : measure α) := rfl

@[simp, norm_cast] lemma coe_fn_zero :
  (⇑(0 : finite_measure α) : set α → ℝ≥0) = (0 : set α → ℝ≥0) := by { funext, refl, }

@[simp, norm_cast] lemma coe_fn_add (μ ν : finite_measure α) :
  (⇑(μ + ν) : set α → ℝ≥0) = (⇑μ + ⇑ν : set α → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe], }

@[simp, norm_cast] lemma coe_fn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] (c : R) (μ : finite_measure α) :
  (⇑(c • μ) : set α → ℝ≥0) = c • (⇑μ : set α → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe, ennreal.coe_smul], }

instance : add_comm_monoid (finite_measure α) :=
coe_injective.add_comm_monoid coe coe_zero coe_add (λ _ _, coe_smul _ _)

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure α →+ measure α :=
{ to_fun := coe, map_zero' := coe_zero, map_add' := coe_add }

instance {α : Type*} [measurable_space α] : module ℝ≥0 (finite_measure α) :=
function.injective.module _ coe_add_monoid_hom coe_injective coe_smul

@[simp] lemma coe_fn_smul_apply [is_scalar_tower R ℝ≥0 ℝ≥0]
  (c : R) (μ : finite_measure α) (s : set α) :
  (c • μ) s  = c • (μ s) :=
by { simp only [coe_fn_smul, pi.smul_apply], }

variables [topological_space α]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def test_against_nn (μ : finite_measure α) (f : α →ᵇ ℝ≥0) : ℝ≥0 :=
(∫⁻ x, f x ∂(μ : measure α)).to_nnreal

lemma _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {α : Type*}
  [topological_space α] [measurable_space α] [opens_measurable_space α] (f : α →ᵇ ℝ≥0) :
  measurable (λ x, (f x : ℝ≥0∞)) :=
measurable_coe_nnreal_ennreal.comp f.continuous.measurable

lemma _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal
  (μ : measure α) [is_finite_measure μ] (f : α →ᵇ ℝ≥0) :
  ∫⁻ x, f x ∂μ < ∞ :=
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

@[simp] lemma test_against_nn_coe_eq {μ : finite_measure α} {f : α →ᵇ ℝ≥0} :
  (μ.test_against_nn f : ℝ≥0∞) = ∫⁻ x, f x ∂(μ : measure α) :=
ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal _ f).ne

lemma test_against_nn_const (μ : finite_measure α) (c : ℝ≥0) :
  μ.test_against_nn (bounded_continuous_function.const α c) = c * μ.mass :=
by simp [← ennreal.coe_eq_coe]

lemma test_against_nn_mono (μ : finite_measure α)
  {f g : α →ᵇ ℝ≥0} (f_le_g : (f : α → ℝ≥0) ≤ g) :
  μ.test_against_nn f ≤ μ.test_against_nn g :=
begin
  simp only [←ennreal.coe_le_coe, test_against_nn_coe_eq],
  exact lintegral_mono (λ x, ennreal.coe_mono (f_le_g x)),
end

@[simp] lemma test_against_nn_zero (μ : finite_measure α) : μ.test_against_nn 0 = 0 :=
by simpa only [zero_mul] using μ.test_against_nn_const 0

@[simp] lemma test_against_nn_one (μ : finite_measure α) : μ.test_against_nn 1 = μ.mass :=
begin
  simp only [test_against_nn, coe_one, pi.one_apply, ennreal.coe_one, lintegral_one],
  refl,
end

@[simp] lemma zero.test_against_nn_apply (f : α →ᵇ ℝ≥0) :
  (0 : finite_measure α).test_against_nn f = 0 :=
by simp only [test_against_nn, coe_zero, lintegral_zero_measure, ennreal.zero_to_nnreal]

lemma zero.test_against_nn : (0 : finite_measure α).test_against_nn = 0 :=
by { funext, simp only [zero.test_against_nn_apply, pi.zero_apply], }

@[simp] lemma smul_test_against_nn_apply (c : ℝ≥0) (μ : finite_measure α) (f : α →ᵇ ℝ≥0) :
  (c • μ).test_against_nn f  = c • (μ.test_against_nn f) :=
by simp only [test_against_nn, coe_smul, smul_eq_mul, ← ennreal.smul_to_nnreal,
  ennreal.smul_def, lintegral_smul_measure]

variables [opens_measurable_space α]

lemma test_against_nn_add (μ : finite_measure α) (f₁ f₂ : α →ᵇ ℝ≥0) :
  μ.test_against_nn (f₁ + f₂) = μ.test_against_nn f₁ + μ.test_against_nn f₂ :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_add, ennreal.coe_add,
             pi.add_apply, test_against_nn_coe_eq],
  exact lintegral_add_left (bounded_continuous_function.nnreal.to_ennreal_comp_measurable _) _
end

lemma test_against_nn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] [pseudo_metric_space R] [has_zero R]
  [has_bounded_smul R ℝ≥0]
  (μ : finite_measure α) (c : R) (f : α →ᵇ ℝ≥0) :
  μ.test_against_nn (c • f) = c • μ.test_against_nn f :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_smul,
             test_against_nn_coe_eq, ennreal.coe_smul],
  simp_rw [←smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ←smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞),
           smul_eq_mul],
  exact @lintegral_const_mul _ _ (μ : measure α) (c • 1)  _
                   (bounded_continuous_function.nnreal.to_ennreal_comp_measurable f),
end

lemma test_against_nn_lipschitz_estimate (μ : finite_measure α) (f g : α →ᵇ ℝ≥0) :
  μ.test_against_nn f ≤ μ.test_against_nn g + (nndist f g) * μ.mass :=
begin
  simp only [←μ.test_against_nn_const (nndist f g), ←test_against_nn_add, ←ennreal.coe_le_coe,
             bounded_continuous_function.coe_add, const_apply, ennreal.coe_add, pi.add_apply,
             coe_nnreal_ennreal_nndist, test_against_nn_coe_eq],
  apply lintegral_mono,
  have le_dist : ∀ x, dist (f x) (g x) ≤ nndist f g :=
  bounded_continuous_function.dist_coe_le_dist,
  intros x,
  have le' : f(x) ≤ g(x) + nndist f g,
  { apply (nnreal.le_add_nndist (f x) (g x)).trans,
    rw add_le_add_iff_left,
    exact dist_le_coe.mp (le_dist x), },
  have le : (f(x) : ℝ≥0∞) ≤ (g(x) : ℝ≥0∞) + (nndist f g),
  by { rw ←ennreal.coe_add, exact ennreal.coe_mono le', },
  rwa [coe_nnreal_ennreal_nndist] at le,
end

lemma test_against_nn_lipschitz (μ : finite_measure α) :
  lipschitz_with μ.mass (λ (f : α →ᵇ ℝ≥0), μ.test_against_nn f) :=
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
def to_weak_dual_bcnn (μ : finite_measure α) :
  weak_dual ℝ≥0 (α →ᵇ ℝ≥0) :=
{ to_fun := λ f, μ.test_against_nn f,
  map_add' := test_against_nn_add μ,
  map_smul' := test_against_nn_smul μ,
  cont := μ.test_against_nn_lipschitz.continuous, }

@[simp] lemma coe_to_weak_dual_bcnn (μ : finite_measure α) :
  ⇑μ.to_weak_dual_bcnn = μ.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : finite_measure α) (f : α →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ x, f x ∂(μ : measure α)).to_nnreal := rfl

/-- The topology of weak convergence on `measure_theory.finite_measure α` is inherited (induced)
from the weak-* topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function
`measure_theory.finite_measure.to_weak_dual_bcnn`. -/
instance : topological_space (finite_measure α) :=
topological_space.induced to_weak_dual_bcnn infer_instance

lemma to_weak_dual_bcnn_continuous :
  continuous (@to_weak_dual_bcnn α _ _ _) :=
continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0) :
  continuous (λ (μ : finite_measure α), μ.test_against_nn f) :=
(by apply (weak_bilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
  continuous ((λ φ : weak_dual ℝ≥0 (α →ᵇ ℝ≥0), φ f) ∘ to_weak_dual_bcnn))

/-- The total mass of a finite measure depends continuously on the measure. -/
lemma continuous_mass : continuous (λ (μ : finite_measure α), μ.mass) :=
by { simp_rw ←test_against_nn_one, exact continuous_test_against_nn_eval 1, }

/-- Convergence of finite measures implies the convergence of their total masses. -/
lemma _root_.filter.tendsto.mass {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure α} {μ : finite_measure α} (h : tendsto μs F (𝓝 μ)) :
  tendsto (λ i, (μs i).mass) F (𝓝 μ.mass) :=
(continuous_mass.tendsto μ).comp h

lemma tendsto_iff_weak_star_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure α} {μ : finite_measure α} :
  tendsto μs F (𝓝 μ) ↔ tendsto (λ i, (μs(i)).to_weak_dual_bcnn) F (𝓝 μ.to_weak_dual_bcnn) :=
inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_to_weak_dual_bcnn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α} {μ : finite_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0), tendsto (λ i, (μs i).to_weak_dual_bcnn f) F (𝓝 (μ.to_weak_dual_bcnn f)) :=
by { rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing], refl, }

theorem tendsto_iff_forall_test_against_nn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α} {μ : finite_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0), tendsto (λ i, (μs i).test_against_nn f) F (𝓝 (μ.test_against_nn f)) :=
by { rw finite_measure.tendsto_iff_forall_to_weak_dual_bcnn_tendsto, refl, }

/-- If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `finite_measure.tendsto_zero_of_tendsto_zero_mass` for
a formulation stating the weak convergence of measures. -/
lemma tendsto_zero_test_against_nn_of_tendsto_zero_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α}
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) (f : α →ᵇ ℝ≥0) :
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
  {μs : γ → finite_measure α} (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) :
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
  {μs : γ → finite_measure α} {μ : finite_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0),
    tendsto (λ i, (∫⁻ x, (f x) ∂(μs(i) : measure α))) F (𝓝 ((∫⁻ x, (f x) ∂(μ : measure α)))) :=
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

variables {α : Type*} [measurable_space α] [topological_space α] [opens_measurable_space α]

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
  (μ : measure α) [is_finite_measure μ] {fs : ι → (α →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (a : α) ∂(μ : measure α), fs i a ≤ c) {f : α → ℝ≥0}
  (fs_lim : ∀ᵐ (a : α) ∂(μ : measure α), tendsto (λ i, fs i a) L (𝓝 (f a))) :
  tendsto (λ i, (∫⁻ a, fs i a ∂μ)) L (𝓝 (∫⁻ a, (f a) ∂μ)) :=
begin
  simpa only using tendsto_lintegral_filter_of_dominated_convergence (λ _, c)
    (eventually_of_forall ((λ i, (ennreal.continuous_coe.comp (fs i).continuous).measurable)))
    _ ((@lintegral_const_lt_top _ _ (μ : measure α) _ _ (@ennreal.coe_ne_top c)).ne) _,
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
lemma tendsto_lintegral_nn_of_le_const (μ : finite_measure α) {fs : ℕ → (α →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ n a, fs n a ≤ c) {f : α → ℝ≥0}
  (fs_lim : ∀ a, tendsto (λ n, fs n a) at_top (𝓝 (f a))) :
  tendsto (λ n, (∫⁻ a, fs n a ∂(μ : measure α))) at_top (𝓝 (∫⁻ a, (f a) ∂(μ : measure α))) :=
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
  [L.is_countably_generated] {μ : finite_measure α} {fs : ι → (α →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (a : α) ∂(μ : measure α), fs i a ≤ c) {f : α →ᵇ ℝ≥0}
  (fs_lim : ∀ᵐ (a : α) ∂(μ : measure α), tendsto (λ i, fs i a) L (𝓝 (f a))) :
  tendsto (λ i, μ.test_against_nn (fs i)) L (𝓝 (μ.test_against_nn f)) :=
begin
  apply (ennreal.tendsto_to_nnreal
         (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure α) f).ne).comp,
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
lemma tendsto_test_against_nn_of_le_const {μ : finite_measure α}
  {fs : ℕ → (α →ᵇ ℝ≥0)} {c : ℝ≥0} (fs_le_const : ∀ n a, fs n a ≤ c) {f : α →ᵇ ℝ≥0}
  (fs_lim : ∀ a, tendsto (λ n, fs n a) at_top (𝓝 (f a))) :
  tendsto (λ n, μ.test_against_nn (fs n)) at_top (𝓝 (μ.test_against_nn f)) :=
tendsto_test_against_nn_filter_of_le_const
  (eventually_of_forall (λ n, eventually_of_forall (fs_le_const n))) (eventually_of_forall fs_lim)

end finite_measure_bounded_convergence -- section

section finite_measure_convergence_by_bounded_continuous_functions
/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/

variables {α : Type*} [measurable_space α] [topological_space α] [opens_measurable_space α]

lemma integrable_of_bounded_continuous_to_nnreal
  (μ : measure α) [is_finite_measure μ] (f : α →ᵇ ℝ≥0) :
  integrable ((coe : ℝ≥0 → ℝ) ∘ ⇑f) μ :=
begin
  refine ⟨(nnreal.continuous_coe.comp f.continuous).measurable.ae_strongly_measurable, _⟩,
  simp only [has_finite_integral, nnreal.nnnorm_eq],
  exact lintegral_lt_top_of_bounded_continuous_to_nnreal _ f,
end

lemma integrable_of_bounded_continuous_to_real
  (μ : measure α) [is_finite_measure μ] (f : α →ᵇ ℝ) :
  integrable ⇑f μ :=
begin
  refine ⟨f.continuous.measurable.ae_strongly_measurable, _⟩,
  have aux : (coe : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = (λ x, ∥f x∥),
  { ext x,
    simp only [function.comp_app, bounded_continuous_function.nnnorm_coe_fun_eq, coe_nnnorm], },
  apply (has_finite_integral_iff_norm ⇑f).mpr,
  rw ← of_real_integral_eq_lintegral_of_real,
  { exact ennreal.of_real_lt_top, },
  { exact aux ▸ integrable_of_bounded_continuous_to_nnreal μ f.nnnorm, },
  { exact eventually_of_forall (λ x, norm_nonneg (f x)), },
end

lemma _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub
  (μ : measure α) [is_finite_measure μ] (f : α →ᵇ ℝ) :
  ∫ x, f x ∂μ = ∫ x, f.nnreal_part x ∂μ - ∫ x, (-f).nnreal_part x ∂μ :=
by simp only [f.self_eq_nnreal_part_sub_nnreal_part_neg,
              pi.sub_apply, integral_sub, integrable_of_bounded_continuous_to_nnreal]

lemma lintegral_lt_top_of_bounded_continuous_to_real
  {α : Type*} [measurable_space α] [topological_space α] (μ : measure α) [is_finite_measure μ]
  (f : α →ᵇ ℝ) :
  ∫⁻ x, ennreal.of_real (f x) ∂μ < ∞ :=
lintegral_lt_top_of_bounded_continuous_to_nnreal _ f.nnreal_part

theorem tendsto_of_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α} {μ : finite_measure α}
  (h : (∀ (f : α →ᵇ ℝ),
       tendsto (λ i, (∫ x, (f x) ∂(μs i : measure α))) F (𝓝 ((∫ x, (f x) ∂(μ : measure α)))))) :
  tendsto μs F (𝓝 μ) :=
begin
  apply (@tendsto_iff_forall_lintegral_tendsto α _ _ _ γ F μs μ).mpr,
  intro f,
  have key := @ennreal.tendsto_to_real_iff _ F
              _ (λ i, (lintegral_lt_top_of_bounded_continuous_to_nnreal (μs i : measure α) f).ne)
              _ (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure α) f).ne,
  simp only [ennreal.of_real_coe_nnreal] at key,
  apply key.mp,
  have lip : lipschitz_with 1 (coe : ℝ≥0 → ℝ), from isometry_subtype_coe.lipschitz,
  set f₀ := bounded_continuous_function.comp _ lip f with def_f₀,
  have f₀_eq : ⇑f₀ = (coe : ℝ≥0 → ℝ) ∘ ⇑f, by refl,
  have f₀_nn : 0 ≤ ⇑f₀, from λ _, by simp only [f₀_eq, pi.zero_apply, nnreal.zero_le_coe],
  have f₀_ae_nn : 0 ≤ᵐ[(μ : measure α)] ⇑f₀, from eventually_of_forall f₀_nn,
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : measure α)] ⇑f₀, from λ i, eventually_of_forall f₀_nn,
  have aux := integral_eq_lintegral_of_nonneg_ae f₀_ae_nn
              f₀.continuous.measurable.ae_strongly_measurable,
  have auxs := λ i, integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i)
              f₀.continuous.measurable.ae_strongly_measurable,
  simp only [f₀_eq, ennreal.of_real_coe_nnreal] at aux auxs,
  simpa only [←aux, ←auxs] using h f₀,
end

lemma _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral
  (f : α →ᵇ ℝ≥0) (μ : measure α) :
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
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α} {μ : finite_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ),
    tendsto (λ i, (∫ x, (f x) ∂(μs i : measure α))) F (𝓝 ((∫ x, (f x) ∂(μ : measure α)))) :=
begin
  refine ⟨_, tendsto_of_forall_integral_tendsto⟩,
  rw tendsto_iff_forall_lintegral_tendsto,
  intros h f,
  simp_rw bounded_continuous_function.integral_eq_integral_nnreal_part_sub,
  set f_pos := f.nnreal_part with def_f_pos,
  set f_neg := (-f).nnreal_part with def_f_neg,
  have tends_pos := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure α) f_pos).ne)).comp (h f_pos),
  have tends_neg := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure α) f_neg).ne)).comp (h f_neg),
  have aux : ∀ (g : α →ᵇ ℝ≥0), ennreal.to_real ∘ (λ (i : γ), ∫⁻ (x : α), ↑(g x) ∂(μs i : measure α))
         = λ (i : γ), (∫⁻ (x : α), ↑(g x) ∂(μs i : measure α)).to_real, from λ _, rfl,
  simp_rw [aux, bounded_continuous_function.nnreal.to_real_lintegral_eq_integral]
          at tends_pos tends_neg,
  exact tendsto.sub tends_pos tends_neg,
end

end finite_measure_convergence_by_bounded_continuous_functions -- section

end finite_measure -- namespace

section probability_measure
/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `α`, denoted by
`measure_theory.probability_measure α`. TODO: Probability measures form a convex space.

If `α` is moreover a topological space and the sigma algebra on `α` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space α]`), then `measure_theory.probability_measure α` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the coercion
`measure_theory.probability_measure.to_finite_measure`.
-/

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measure (α : Type*) [measurable_space α] : Type* :=
{μ : measure α // is_probability_measure μ}

namespace probability_measure

variables {α : Type*} [measurable_space α]

instance [inhabited α] : inhabited (probability_measure α) :=
⟨⟨measure.dirac default, measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : has_coe (probability_measure α) (measure_theory.measure α) := coe_subtype

instance : has_coe_to_fun (probability_measure α) (λ _, set α → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

instance (μ : probability_measure α) : is_probability_measure (μ : measure α) := μ.prop

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : probability_measure α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

@[simp] lemma val_eq_to_measure (ν : probability_measure α) : ν.val = (ν : measure α) := rfl

lemma coe_injective : function.injective (coe : probability_measure α → measure α) :=
subtype.coe_injective

@[simp] lemma coe_fn_univ (ν : probability_measure α) : ν univ = 1 :=
congr_arg ennreal.to_nnreal ν.prop.measure_univ

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measure α) : finite_measure α := ⟨μ, infer_instance⟩

@[simp] lemma coe_comp_to_finite_measure_eq_coe (ν : probability_measure α) :
  (ν.to_finite_measure : measure α) = (ν : measure α) := rfl

@[simp] lemma coe_fn_comp_to_finite_measure_eq_coe_fn (ν : probability_measure α) :
  (ν.to_finite_measure : set α → ℝ≥0) = (ν : set α → ℝ≥0) := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : probability_measure α) (s : set α) :
  (ν s : ℝ≥0∞) = (ν : measure α) s :=
by rw [← coe_fn_comp_to_finite_measure_eq_coe_fn,
  finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure, coe_comp_to_finite_measure_eq_coe]

@[ext] lemma extensionality (μ ν : probability_measure α)
  (h : ∀ (s : set α), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1, ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

@[simp] lemma mass_to_finite_measure (μ : probability_measure α) :
  μ.to_finite_measure.mass = 1 := μ.coe_fn_univ

lemma to_finite_measure_nonzero (μ : probability_measure α) :
  μ.to_finite_measure ≠ 0 :=
begin
  intro maybe_zero,
  have mass_zero := (finite_measure.mass_zero_iff _).mpr maybe_zero,
  rw μ.mass_to_finite_measure at mass_zero,
  exact one_ne_zero mass_zero,
end

variables [topological_space α] [opens_measurable_space α]

lemma test_against_nn_lipschitz (μ : probability_measure α) :
  lipschitz_with 1 (λ (f : α →ᵇ ℝ≥0), μ.to_finite_measure.test_against_nn f) :=
μ.mass_to_finite_measure ▸ μ.to_finite_measure.test_against_nn_lipschitz

/-- The topology of weak convergence on `measure_theory.probability_measure α`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`measure_theory.probability_measure.to_finite_measure`. -/
instance : topological_space (probability_measure α) :=
topological_space.induced to_finite_measure infer_instance

lemma to_finite_measure_continuous :
  continuous (to_finite_measure : probability_measure α → finite_measure α) :=
continuous_induced_dom

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bcnn : probability_measure α → weak_dual ℝ≥0 (α →ᵇ ℝ≥0) :=
finite_measure.to_weak_dual_bcnn ∘ to_finite_measure

@[simp] lemma coe_to_weak_dual_bcnn (μ : probability_measure α) :
  ⇑μ.to_weak_dual_bcnn = μ.to_finite_measure.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : probability_measure α) (f : α →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ x, f x ∂(μ : measure α)).to_nnreal := rfl

lemma to_weak_dual_bcnn_continuous :
  continuous (λ (μ : probability_measure α), μ.to_weak_dual_bcnn) :=
finite_measure.to_weak_dual_bcnn_continuous.comp to_finite_measure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0) :
  continuous (λ (μ : probability_measure α), μ.to_finite_measure.test_against_nn f) :=
(finite_measure.continuous_test_against_nn_eval f).comp to_finite_measure_continuous

/- The canonical mapping from probability measures to finite measures is an embedding. -/
lemma to_finite_measure_embedding (α : Type*)
  [measurable_space α] [topological_space α] [opens_measurable_space α] :
  embedding (to_finite_measure : probability_measure α → finite_measure α) :=
{ induced := rfl,
  inj := λ μ ν h, subtype.eq (by convert congr_arg coe h) }

lemma tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type*}
  (F : filter δ) {μs : δ → probability_measure α} {μ₀ : probability_measure α} :
  tendsto μs F (𝓝 μ₀) ↔ tendsto (to_finite_measure ∘ μs) F (𝓝 (μ₀.to_finite_measure)) :=
embedding.tendsto_nhds_iff (to_finite_measure_embedding α)

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → probability_measure α} {μ : probability_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0), tendsto (λ i, (∫⁻ x, (f x) ∂(μs(i) : measure α))) F
    (𝓝 ((∫⁻ x, (f x) ∂(μ : measure α)))) :=
begin
  rw tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
  exact finite_measure.tendsto_iff_forall_lintegral_tendsto,
end

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → probability_measure α} {μ : probability_measure α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ),
    tendsto (λ i, (∫ x, (f x) ∂(μs i : measure α))) F (𝓝 ((∫ x, (f x) ∂(μ : measure α)))) :=
begin
  rw tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
  rw finite_measure.tendsto_iff_forall_integral_tendsto,
  simp only [coe_comp_to_finite_measure_eq_coe],
end

end probability_measure -- namespace

end probability_measure -- section

section normalize_finite_measure
/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace finite_measure

variables {α : Type*} [nonempty α] {m0 : measurable_space α} (μ : finite_measure α)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
def normalize : probability_measure α :=
if zero : μ.mass = 0 then ⟨measure.dirac ‹nonempty α›.some, measure.dirac.is_probability_measure⟩
  else {  val := (μ.mass)⁻¹ • μ,
          property := begin
            refine ⟨_⟩,
            simp only [mass, measure.coe_nnreal_smul_apply,
                        ←ennreal_coe_fn_eq_coe_fn_to_measure μ univ],
            norm_cast,
            exact inv_mul_cancel zero,
          end }

@[simp] lemma self_eq_mass_mul_normalize (s : set α) : μ s = μ.mass * μ.normalize s :=
begin
  by_cases μ = 0,
  { rw h,
    simp only [zero.mass, coe_fn_zero, pi.zero_apply, zero_mul], },
  have mass_nonzero : μ.mass ≠ 0, by rwa μ.mass_nonzero_iff,
  simp only [(show μ ≠ 0, from h), mass_nonzero, normalize, not_false_iff, dif_neg],
  change μ s = μ.mass * ((μ.mass)⁻¹ • μ) s,
  rw coe_fn_smul_apply,
  simp only [mass_nonzero, algebra.id.smul_eq_mul, mul_inv_cancel_left₀, ne.def, not_false_iff],
end

lemma self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.to_finite_measure :=
begin
  ext s s_mble,
  rw [μ.self_eq_mass_mul_normalize s, coe_fn_smul_apply],
  refl,
end

lemma normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : set α) :
  μ.normalize s = (μ.mass)⁻¹ * (μ s) :=
by simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero,
              inv_mul_cancel_left₀, ne.def, not_false_iff]

lemma normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ ≠ 0) :
  μ.normalize.to_finite_measure = (μ.mass)⁻¹ • μ :=
begin
  nth_rewrite 2 μ.self_eq_mass_smul_normalize,
  rw ← smul_assoc,
  simp only [μ.mass_nonzero_iff.mpr nonzero, algebra.id.smul_eq_mul,
             inv_mul_cancel, ne.def, not_false_iff, one_smul],
end

lemma coe_normalize_eq_of_nonzero (nonzero : μ ≠ 0) : (μ.normalize : measure α) = (μ.mass)⁻¹ • μ :=
begin
  ext1 s s_mble,
  simp only [← μ.normalize.ennreal_coe_fn_eq_coe_fn_to_measure s,
             μ.normalize_eq_of_nonzero nonzero s, ennreal.coe_mul,
             ennreal_coe_fn_eq_coe_fn_to_measure, measure.coe_nnreal_smul_apply],
end

@[simp] lemma _root_.probability_measure.to_finite_measure_normalize_eq_self
  {m0 : measurable_space α} (μ : probability_measure α) :
  μ.to_finite_measure.normalize = μ :=
begin
  ext s s_mble,
  rw μ.to_finite_measure.normalize_eq_of_nonzero μ.to_finite_measure_nonzero s,
  simp only [probability_measure.mass_to_finite_measure, inv_one, one_mul],
  refl,
end

/-- Averaging with respect to a finite measure is the same as integraing against
`measure_theory.finite_measure.normalize`. -/
lemma average_eq_integral_normalize
  {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  (nonzero : μ ≠ 0) (f : α → E) :
  average (μ : measure α) f = ∫ x, f x ∂(μ.normalize : measure α) :=
begin
  rw [μ.coe_normalize_eq_of_nonzero nonzero, average],
  congr,
  simp only [ring_hom.to_fun_eq_coe, ennreal.coe_of_nnreal_hom,
             ennreal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass],
end

variables [topological_space α]

lemma test_against_nn_eq_mass_mul (f : α →ᵇ ℝ≥0) :
  μ.test_against_nn f = μ.mass * μ.normalize.to_finite_measure.test_against_nn f :=
begin
  nth_rewrite 0 μ.self_eq_mass_smul_normalize,
  rw μ.normalize.to_finite_measure.smul_test_against_nn_apply μ.mass f,
  refl,
end

lemma normalize_test_against_nn (nonzero : μ ≠ 0) (f : α →ᵇ ℝ≥0) :
  μ.normalize.to_finite_measure.test_against_nn f = (μ.mass)⁻¹ * μ.test_against_nn f :=
by simp [μ.test_against_nn_eq_mass_mul, μ.mass_nonzero_iff.mpr nonzero]

variables [opens_measurable_space α]

variables {μ}

lemma tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α}
  (μs_lim : tendsto (λ i, (μs i).normalize) F (𝓝 μ.normalize))
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 μ.mass)) (f : α →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).test_against_nn f) F (𝓝 (μ.test_against_nn f)) :=
begin
  by_cases h_mass : μ.mass = 0,
  { simp only [μ.mass_zero_iff.mp h_mass, zero.test_against_nn_apply,
               zero.mass, eq_self_iff_true] at *,
    exact tendsto_zero_test_against_nn_of_tendsto_zero_mass mass_lim f, },
  simp_rw [(λ i, (μs i).test_against_nn_eq_mass_mul f), μ.test_against_nn_eq_mass_mul f],
  rw probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds at μs_lim,
  rw tendsto_iff_forall_test_against_nn_tendsto at μs_lim,
  have lim_pair : tendsto
        (λ i, (⟨(μs i).mass, (μs i).normalize.to_finite_measure.test_against_nn f⟩ : ℝ≥0 × ℝ≥0))
        F (𝓝 (⟨μ.mass, μ.normalize.to_finite_measure.test_against_nn f⟩)),
    from (prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩,
  exact tendsto_mul.comp lim_pair,
end

lemma tendsto_normalize_test_against_nn_of_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure α} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : α →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).normalize.to_finite_measure.test_against_nn f) F
          (𝓝 (μ.normalize.to_finite_measure.test_against_nn f)) :=
begin
  have lim_mass := μs_lim.mass,
  have aux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 (μ.mass),
    from is_open_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero),
  have eventually_nonzero : ∀ᶠ i in F, μs i ≠ 0,
  { simp_rw ← mass_nonzero_iff,
    exact lim_mass aux, },
  have eve : ∀ᶠ i in F,
    (μs i).normalize.to_finite_measure.test_against_nn f
    = ((μs i).mass)⁻¹ * (μs i).test_against_nn f,
  { filter_upwards [eventually_iff.mp eventually_nonzero],
    intros i hi,
    apply normalize_test_against_nn _ hi, },
  simp_rw [tendsto_congr' eve, μ.normalize_test_against_nn nonzero],
  have lim_pair : tendsto
        (λ i, (⟨((μs i).mass)⁻¹, (μs i).test_against_nn f⟩ : ℝ≥0 × ℝ≥0))
        F (𝓝 (⟨(μ.mass)⁻¹, μ.test_against_nn f⟩)),
  { refine (prod.tendsto_iff _ _).mpr ⟨_, _⟩,
    { exact (continuous_on_inv₀.continuous_at aux).tendsto.comp lim_mass, },
    { exact tendsto_iff_forall_test_against_nn_tendsto.mp μs_lim f, }, },
  exact tendsto_mul.comp lim_pair,
end

/-- If the normalized versions of finite measures converge weakly and their total masses
also converge, then the finite measures themselves converge weakly. -/
lemma tendsto_of_tendsto_normalize_test_against_nn_of_tendsto_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure α}
  (μs_lim : tendsto (λ i, (μs i).normalize) F (𝓝 μ.normalize))
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 μ.mass)) :
  tendsto μs F (𝓝 μ) :=
begin
  rw tendsto_iff_forall_test_against_nn_tendsto,
  exact λ f, tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass
             μs_lim mass_lim f,
end

/-- If finite measures themselves converge weakly to a nonzero limit measure, then their
normalized versions also converge weakly. -/
lemma tendsto_normalize_of_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure α} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
  tendsto (λ i, (μs i).normalize) F (𝓝 (μ.normalize)) :=
begin
  rw [probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
      tendsto_iff_forall_test_against_nn_tendsto],
  exact λ f, tendsto_normalize_test_against_nn_of_tendsto μs_lim nonzero f,
end

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure α} (nonzero : μ ≠ 0) :
  tendsto (λ i, (μs i).normalize) F (𝓝 (μ.normalize)) ∧ tendsto (λ i, (μs i).mass) F (𝓝 (μ.mass))
  ↔ tendsto μs F (𝓝 μ) :=
begin
  split,
  { rintros ⟨normalized_lim, mass_lim⟩,
    exact tendsto_of_tendsto_normalize_test_against_nn_of_tendsto_mass normalized_lim mass_lim, },
  { intro μs_lim,
    refine ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩, },
end

end finite_measure --namespace

end normalize_finite_measure -- section

section convergence_implies_limsup_closed_le
/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `α` is
pseudo-emetrizable, that the weak convergence of measures on `measure_theory.finite_measure α`
implies that for any closed set `F` in `α` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.
-/

variables {α : Type*} [measurable_space α]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
lemma measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : filter ι}
  [L.is_countably_generated] [topological_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {c : ℝ≥0} {E : set α} (E_mble : measurable_set E)
  (fs : ι → (α →ᵇ ℝ≥0)) (fs_bdd : ∀ᶠ i in L, ∀ᵐ (a : α) ∂μ, fs i a ≤ c)
  (fs_lim : ∀ᵐ (a : α) ∂μ,
            tendsto (λ (i : ι), (coe_fn : (α →ᵇ ℝ≥0) → (α → ℝ≥0)) (fs i) a) L
                    (𝓝 (indicator E (λ x, (1 : ℝ≥0)) a))) :
  tendsto (λ n, lintegral μ (λ a, fs n a)) L (𝓝 (μ E)) :=
begin
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim,
  have aux : ∀ a, indicator E (λ x, (1 : ℝ≥0∞)) a = ↑(indicator E (λ x, (1 : ℝ≥0)) a),
  from λ a, by simp only [ennreal.coe_indicator, ennreal.coe_one],
  simp_rw [←aux, lintegral_indicator _ E_mble],
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
end

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
lemma measure_of_cont_bdd_of_tendsto_indicator
  [topological_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {c : ℝ≥0} {E : set α} (E_mble : measurable_set E)
  (fs : ℕ → (α →ᵇ ℝ≥0)) (fs_bdd : ∀ n a, fs n a ≤ c)
  (fs_lim : tendsto (λ (n : ℕ), (coe_fn : (α →ᵇ ℝ≥0) → (α → ℝ≥0)) (fs n))
            at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0))))) :
  tendsto (λ n, lintegral μ (λ a, fs n a)) at_top (𝓝 (μ E)) :=
begin
  have fs_lim' : ∀ a, tendsto (λ (n : ℕ), (fs n a : ℝ≥0))
                 at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0)) a)),
  by { rw tendsto_pi_nhds at fs_lim, exact λ a, fs_lim a, },
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall (λ n, eventually_of_forall (fs_bdd n))) (eventually_of_forall fs_lim'),
end

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
lemma tendsto_lintegral_thickened_indicator_of_is_closed
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {F : set α} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, lintegral μ (λ a, (thickened_indicator (δs_pos n) F a : ℝ≥0∞)))
          at_top (𝓝 (μ F)) :=
begin
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set
          (λ n, thickened_indicator (δs_pos n) F)
          (λ n a, thickened_indicator_le_one (δs_pos n) F a),
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F,
  rwa F_closed.closure_eq at key,
end

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
lemma finite_measure.limsup_measure_closed_le_of_tendsto
  {α ι : Type*} {L : filter ι}
  [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  {μ : finite_measure α} {μs : ι → finite_measure α}
  (μs_lim : tendsto μs L (𝓝 μ)) {F : set α} (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure α) F) ≤ (μ : measure α) F :=
begin
  by_cases L = ⊥,
  { simp only [h, limsup, filter.map_bot, Limsup_bot, ennreal.bot_eq_zero, zero_le], },
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μ_F_finite,
  set δs := λ (n : ℕ), (1 : ℝ) / (n+1) with def_δs,
  have δs_pos : ∀ n, 0 < δs n, from λ n, nat.one_div_pos_of_nat,
  have δs_lim : tendsto δs at_top (𝓝 0), from tendsto_one_div_add_at_top_nhds_0_nat,
  have key₁ := tendsto_lintegral_thickened_indicator_of_is_closed
                  (μ : measure α) F_closed δs_pos δs_lim,
  have room₁ : (μ : measure α) F < (μ : measure α) F + ε / 2,
  { apply ennreal.lt_add_right (measure_lt_top (μ : measure α) F).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩,
  have key₂ := finite_measure.tendsto_iff_forall_lintegral_tendsto.mp
                μs_lim (thickened_indicator (δs_pos M) F),
  have room₂ : lintegral (μ : measure α) (λ a, thickened_indicator (δs_pos M) F a)
                < lintegral (μ : measure α) (λ a, thickened_indicator (δs_pos M) F a) + ε / 2,
  { apply ennreal.lt_add_right
          (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure α) _).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) (λ n, le_of_lt),
  have aux := λ n, le_trans (measure_le_lintegral_thickened_indicator
                            (μs n : measure α) F_closed.measurable_set (δs_pos M)),
  have ev_near' := eventually.mono ev_near aux,
  apply (filter.limsup_le_limsup ev_near').trans,
  haveI : ne_bot L, from ⟨h⟩,
  rw limsup_const,
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε/2 : ℝ≥0∞))),
  simp only [add_assoc, ennreal.add_halves, le_refl],
end

end convergence_implies_limsup_closed_le --section

end measure_theory --namespace
