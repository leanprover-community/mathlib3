/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.measure.finite_measure
import measure_theory.integral.average

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
 * the type `measure_theory.probability_measure Ω` with the topology of convergence in
   distribution (a.k.a. convergence in law, weak convergence of measures);
 * `measure_theory.probability_measure.to_finite_measure`: Interpret a probability measure as
   a finite measure;
 * `measure_theory.finite_measure.normalize`: Normalize a finite measure to a probability measure
   (returns junk for the zero measure).

## Main results

 * `measure_theory.probability_measure.tendsto_iff_forall_integral_tendsto`: Convergence of
   probability measures is characterized by the convergence of expected values of all bounded
   continuous random variables. This shows that the chosen definition of topology coincides with
   the common textbook definition of convergence in distribution, i.e., weak convergence of
   measures. A similar characterization by the convergence of expected values (in the
   `measure_theory.lintegral` sense) of all bounded continuous nonnegative random variables is
   `measure_theory.probability_measure.tendsto_iff_forall_lintegral_tendsto`.
 * `measure_theory.finite_measure.tendsto_normalize_iff_tendsto`: The convergence of finite
   measures to a nonzero limit is characterized by the convergence of the probability-normalized
   versions and of the total masses.

TODO:
 * Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `measure_theory.probability_measure Ω` is inherited
weak convergence of finite measures via the mapping
`measure_theory.probability_measure.to_finite_measure`.

Like `measure_theory.finite_measure Ω`, the implementation of `measure_theory.probability_measure Ω`
is directly as a subtype of `measure_theory.measure Ω`, and the coercion to a function is the
composition `ennreal.to_nnreal` and the coercion to function of `measure_theory.measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topology ennreal nnreal bounded_continuous_function

namespace measure_theory

section probability_measure
/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`measure_theory.probability_measure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space Ω]`), then `measure_theory.probability_measure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`measure_theory.probability_measure.to_finite_measure`.
-/

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measure (Ω : Type*) [measurable_space Ω] : Type* :=
{μ : measure Ω // is_probability_measure μ}

namespace probability_measure

variables {Ω : Type*} [measurable_space Ω]

instance [inhabited Ω] : inhabited (probability_measure Ω) :=
⟨⟨measure.dirac default, measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : has_coe (probability_measure Ω) (measure_theory.measure Ω) := coe_subtype

instance : has_coe_to_fun (probability_measure Ω) (λ _, set Ω → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

instance (μ : probability_measure Ω) : is_probability_measure (μ : measure Ω) := μ.prop

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : probability_measure Ω) :
  (ν : set Ω → ℝ≥0) = λ s, ((ν : measure Ω) s).to_nnreal := rfl

@[simp] lemma val_eq_to_measure (ν : probability_measure Ω) : ν.val = (ν : measure Ω) := rfl

lemma coe_injective : function.injective (coe : probability_measure Ω → measure Ω) :=
subtype.coe_injective

@[simp] lemma coe_fn_univ (ν : probability_measure Ω) : ν univ = 1 :=
congr_arg ennreal.to_nnreal ν.prop.measure_univ

lemma coe_fn_univ_ne_zero (ν : probability_measure Ω) : ν univ ≠ 0 :=
by simp only [coe_fn_univ, ne.def, one_ne_zero, not_false_iff]

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measure Ω) : finite_measure Ω := ⟨μ, infer_instance⟩

@[simp] lemma coe_comp_to_finite_measure_eq_coe (ν : probability_measure Ω) :
  (ν.to_finite_measure : measure Ω) = (ν : measure Ω) := rfl

@[simp] lemma coe_fn_comp_to_finite_measure_eq_coe_fn (ν : probability_measure Ω) :
  (ν.to_finite_measure : set Ω → ℝ≥0) = (ν : set Ω → ℝ≥0) := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : probability_measure Ω) (s : set Ω) :
  (ν s : ℝ≥0∞) = (ν : measure Ω) s :=
by rw [← coe_fn_comp_to_finite_measure_eq_coe_fn,
  finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure, coe_comp_to_finite_measure_eq_coe]

lemma apply_mono (μ : probability_measure Ω) {s₁ s₂ : set Ω} (h : s₁ ⊆ s₂) :
  μ s₁ ≤ μ s₂ :=
begin
  rw ← coe_fn_comp_to_finite_measure_eq_coe_fn,
  exact measure_theory.finite_measure.apply_mono _ h,
end

lemma nonempty_of_probability_measure (μ : probability_measure Ω) : nonempty Ω :=
begin
  by_contra maybe_empty,
  have zero : (μ : measure Ω) univ = 0,
    by rw [univ_eq_empty_iff.mpr (not_nonempty_iff.mp maybe_empty), measure_empty],
  rw measure_univ at zero,
  exact zero_ne_one zero.symm,
end

@[ext] lemma eq_of_forall_measure_apply_eq (μ ν : probability_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → (μ : measure Ω) s = (ν : measure Ω) s) :
  μ = ν :=
by { ext1, ext1 s s_mble, exact h s s_mble, }

lemma eq_of_forall_apply_eq (μ ν : probability_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

@[simp] lemma mass_to_finite_measure (μ : probability_measure Ω) :
  μ.to_finite_measure.mass = 1 := μ.coe_fn_univ

lemma to_finite_measure_nonzero (μ : probability_measure Ω) :
  μ.to_finite_measure ≠ 0 :=
begin
  rw [←finite_measure.mass_nonzero_iff, μ.mass_to_finite_measure],
  exact one_ne_zero,
end

variables [topological_space Ω] [opens_measurable_space Ω]

lemma test_against_nn_lipschitz (μ : probability_measure Ω) :
  lipschitz_with 1 (λ (f : Ω →ᵇ ℝ≥0), μ.to_finite_measure.test_against_nn f) :=
μ.mass_to_finite_measure ▸ μ.to_finite_measure.test_against_nn_lipschitz

/-- The topology of weak convergence on `measure_theory.probability_measure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`measure_theory.probability_measure.to_finite_measure`. -/
instance : topological_space (probability_measure Ω) :=
topological_space.induced to_finite_measure infer_instance

lemma to_finite_measure_continuous :
  continuous (to_finite_measure : probability_measure Ω → finite_measure Ω) :=
continuous_induced_dom

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bcnn : probability_measure Ω → weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
finite_measure.to_weak_dual_bcnn ∘ to_finite_measure

@[simp] lemma coe_to_weak_dual_bcnn (μ : probability_measure Ω) :
  ⇑μ.to_weak_dual_bcnn = μ.to_finite_measure.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : probability_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ ω, f ω ∂(μ : measure Ω)).to_nnreal := rfl

lemma to_weak_dual_bcnn_continuous :
  continuous (λ (μ : probability_measure Ω), μ.to_weak_dual_bcnn) :=
finite_measure.to_weak_dual_bcnn_continuous.comp to_finite_measure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : Ω →ᵇ ℝ≥0) :
  continuous (λ (μ : probability_measure Ω), μ.to_finite_measure.test_against_nn f) :=
(finite_measure.continuous_test_against_nn_eval f).comp to_finite_measure_continuous

/- The canonical mapping from probability measures to finite measures is an embedding. -/
lemma to_finite_measure_embedding (Ω : Type*)
  [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω] :
  embedding (to_finite_measure : probability_measure Ω → finite_measure Ω) :=
{ induced := rfl,
  inj := λ μ ν h, subtype.eq (by convert congr_arg coe h) }

lemma tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type*}
  (F : filter δ) {μs : δ → probability_measure Ω} {μ₀ : probability_measure Ω} :
  tendsto μs F (𝓝 μ₀) ↔ tendsto (to_finite_measure ∘ μs) F (𝓝 (μ₀.to_finite_measure)) :=
embedding.tendsto_nhds_iff (to_finite_measure_embedding Ω)

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → probability_measure Ω} {μ : probability_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (∫⁻ ω, (f ω) ∂(μs(i) : measure Ω))) F
    (𝓝 ((∫⁻ ω, (f ω) ∂(μ : measure Ω)))) :=
begin
  rw tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
  exact finite_measure.tendsto_iff_forall_lintegral_tendsto,
end

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → probability_measure Ω} {μ : probability_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ),
    tendsto (λ i, (∫ ω, (f ω) ∂(μs i : measure Ω))) F (𝓝 ((∫ ω, (f ω) ∂(μ : measure Ω)))) :=
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

variables {Ω : Type*} [nonempty Ω] {m0 : measurable_space Ω} (μ : finite_measure Ω)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
def normalize : probability_measure Ω :=
if zero : μ.mass = 0 then ⟨measure.dirac ‹nonempty Ω›.some, measure.dirac.is_probability_measure⟩
  else {  val := (μ.mass)⁻¹ • μ,
          property := begin
            refine ⟨_⟩,
            simp only [mass, measure.coe_nnreal_smul_apply,
                        ←ennreal_coe_fn_eq_coe_fn_to_measure μ univ],
            norm_cast,
            exact inv_mul_cancel zero,
          end }

@[simp] lemma self_eq_mass_mul_normalize (s : set Ω) : μ s = μ.mass * μ.normalize s :=
begin
  obtain rfl|h := eq_or_ne μ 0,
  { simp only [zero.mass, coe_fn_zero, pi.zero_apply, zero_mul], },
  have mass_nonzero : μ.mass ≠ 0, by rwa μ.mass_nonzero_iff,
  simp only [normalize, dif_neg mass_nonzero, ennreal.to_nnreal_mul, subtype.coe_mk,
    probability_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure, ennreal.to_nnreal_coe,
    measure_theory.measure.coe_nnreal_smul_apply, mul_inv_cancel_left₀ mass_nonzero,
    finite_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure],
end

lemma self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.to_finite_measure :=
begin
  apply eq_of_forall_apply_eq,
  intros s s_mble,
  rw [μ.self_eq_mass_mul_normalize s, coe_fn_smul_apply, smul_eq_mul,
    probability_measure.coe_fn_comp_to_finite_measure_eq_coe_fn],
end

lemma normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : set Ω) :
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

lemma coe_normalize_eq_of_nonzero (nonzero : μ ≠ 0) : (μ.normalize : measure Ω) = (μ.mass)⁻¹ • μ :=
begin
  ext1 s s_mble,
  simp only [← μ.normalize.ennreal_coe_fn_eq_coe_fn_to_measure s,
             μ.normalize_eq_of_nonzero nonzero s, ennreal.coe_mul,
             ennreal_coe_fn_eq_coe_fn_to_measure, measure.coe_nnreal_smul_apply],
end

@[simp] lemma _root_.probability_measure.to_finite_measure_normalize_eq_self
  {m0 : measurable_space Ω} (μ : probability_measure Ω) :
  μ.to_finite_measure.normalize = μ :=
begin
  apply probability_measure.eq_of_forall_apply_eq,
  intros s s_mble,
  rw μ.to_finite_measure.normalize_eq_of_nonzero μ.to_finite_measure_nonzero s,
  simp only [probability_measure.mass_to_finite_measure, inv_one, one_mul,
             probability_measure.coe_fn_comp_to_finite_measure_eq_coe_fn],
end

/-- Averaging with respect to a finite measure is the same as integraing against
`measure_theory.finite_measure.normalize`. -/
lemma average_eq_integral_normalize
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  (nonzero : μ ≠ 0) (f : Ω → E) :
  average (μ : measure Ω) f = ∫ ω, f ω ∂(μ.normalize : measure Ω) :=
begin
  rw [μ.coe_normalize_eq_of_nonzero nonzero, average],
  congr,
  simp only [ring_hom.to_fun_eq_coe, ennreal.coe_of_nnreal_hom,
             ennreal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass],
end

variables [topological_space Ω]

lemma test_against_nn_eq_mass_mul (f : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn f = μ.mass * μ.normalize.to_finite_measure.test_against_nn f :=
begin
  nth_rewrite 0 μ.self_eq_mass_smul_normalize,
  rw [μ.normalize.to_finite_measure.smul_test_against_nn_apply μ.mass f, smul_eq_mul],
end

lemma normalize_test_against_nn (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
  μ.normalize.to_finite_measure.test_against_nn f = (μ.mass)⁻¹ * μ.test_against_nn f :=
by simp [μ.test_against_nn_eq_mass_mul, μ.mass_nonzero_iff.mpr nonzero]

variables [opens_measurable_space Ω]

variables {μ}

lemma tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
  (μs_lim : tendsto (λ i, (μs i).normalize) F (𝓝 μ.normalize))
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 μ.mass)) (f : Ω →ᵇ ℝ≥0) :
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
  {μs : γ → finite_measure Ω} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
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
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
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
  {μs : γ → finite_measure Ω} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
  tendsto (λ i, (μs i).normalize) F (𝓝 (μ.normalize)) :=
begin
  rw [probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
      tendsto_iff_forall_test_against_nn_tendsto],
  exact λ f, tendsto_normalize_test_against_nn_of_tendsto μs_lim nonzero f,
end

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (nonzero : μ ≠ 0) :
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

end measure_theory
