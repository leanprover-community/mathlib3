/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.bochner_integration

/-!
# Weak convergence of finite Borel measures and Borel probability measures

In this file we introduce `probability_measures α` and `finite_measures α` for any measurable
space α. Both are defined as subtypes of measures on α. When the measurable space α is a
topological space with its Borel sigma algebra, we define a topology on `probability_measures α`
and on `finite_measures α`, which corresponds to the weak convergence of measures.

## Main results

- `weak_conv_seq_iff'`: A characterization of the weak convergence of a sequence of Borel
  probability measures in terms of integrals of nonnegative bounded continuous functions.
- WIP: Future versions will include many other equivalent characterizations of the weak convergence
  of a sequence of Borel probability measures (Portmanteau theorem).

## Notation

 - No new notation is introduced.

## References

Weak convergence of measures in Wikipedia:
<https://en.wikipedia.org/wiki/Convergence_of_measures#Weak_convergence_of_measures>

A standard textbook about the weak convergence of Borel probability measures is [Billingsley1999].

[Billingsley1999] Billingsley, Patrick (1999). Convergence of Probability Measures. New York, NY:
John Wiley & Sons, Inc. ISBN 0-471-19745-9.
-/

noncomputable theory
open measure_theory
open filter
open_locale topological_space
open_locale bounded_continuous_function

-- TODO: What is the appropriate place for this definition suggested by Floris?
def bounded_above {α β : Type*} [has_le β] [has_top β] (f : α → β) : Prop :=
∃ (M : β), M ≠ ⊤ ∧ ∀ (a : α), f(a) ≤ M

namespace weak_convergence

section test_functions_for_weak_convergence

/-!
### Test functions for weak convergence of measures

Weak convergence of measures will be defined in terms of integrating suitable test functions
against the measures. As suitable test functions, we choose nonnegative bounded continuous
functions. In this section, we define the type `bounded_continuous_to_ennreal α` of such
test functions on a topological space α and the type
`functional_on_bounded_continuous_to_ennreal α`. The latter is equipped with the topology
of pointwise ("testfunctionwise") convergence.
-/

universes u

variables {α : Type*} [topological_space α]

/-- The type `bounded_continuous_to_ennreal α` consists of continuous bounded functions on
a topological space `α` with values in `ennreal`. Such functions are used as "test functions" in
the definition of the topology of the weak convergence of probability measures. -/
structure bounded_continuous_to_ennreal (α : Type*) [topological_space α]
  extends continuous_map α ennreal :=
(bounded_above' : bounded_above to_fun)

instance bounded_continuous_to_ennreal.has_coe_to_fun :
  has_coe_to_fun (bounded_continuous_to_ennreal α) := ⟨λ _, α → ennreal, λ f, f.to_fun⟩

@[simp] lemma bounded_continuous_to_ennreal.to_fun_eq_coe (f : bounded_continuous_to_ennreal α) :
  f.to_fun = f := rfl

def bounded_continuous_to_ennreal.mk' (f : α → ennreal)
  (f_cont : continuous f) (f_bdd : bounded_above f) : bounded_continuous_to_ennreal α :=
{ to_fun := f,
  continuous_to_fun := f_cont,
  bounded_above' := f_bdd, }

-- @[simp] ?
lemma continuous_of_bounded_continuous_to_ennreal (f : bounded_continuous_to_ennreal α) :
  continuous (f : α → ennreal) := f.to_continuous_map.continuous

-- @[simp] ?
lemma borel_measurable_of_bounded_continuous_to_ennreal [measurable_space α] [borel_space α]
  (f : bounded_continuous_to_ennreal α) : measurable (f : α → ennreal) :=
continuous.measurable (continuous_of_bounded_continuous_to_ennreal f)

/-- The type `functional_on_bounded_continuous_to_ennreal` consists of continuous bounded functions
on the type `bounded_continuous_to_ennreal α` of "test functions" for weak convergence. Such
functionals are by construction positive (by the choice of `ennreal` as their codomain), but there
is no a priori requirement of continuity.
(To define the usual continuity, one should equip `bounded_continuous_to_ennreal α` with
the topology determined by the sup-norm-like metric. Riesz-Markov-Kakutani representation theorem
would then identify the continuous positive functionals as finite measures.) -/
def functional_on_bounded_continuous_to_ennreal (α : Type*) [topological_space α] : Type* :=
(bounded_continuous_to_ennreal α) → ennreal

instance functional_on_bounded_continuous_to_ennreal.has_coe_to_fun :
  has_coe_to_fun (functional_on_bounded_continuous_to_ennreal α) :=
⟨λ _, (bounded_continuous_to_ennreal α) → ennreal, λ φ, φ⟩

/-- As a first step towards the definition of the topology of the weak convergence of probability
measures, the space of functionals `(cont_bdd_ennval α) → ennreal` is equipped with the product
topology (the topology of "testfunctionwise" convergence, i.e., of pointwise convergence of the
functionals defined on the space of continuous bounded test functions). -/
instance : topological_space (functional_on_bounded_continuous_to_ennreal α) :=
Pi.topological_space

end test_functions_for_weak_convergence

section topology_of_weak_convergence

/-!
### Topology of weak convergence of measures

In this section, we define the topology of weak convergence on the set of Borel probability
measures and on the set of finite Borel measures on a topological space.
-/

def probability_measures (α : Type*) [measurable_space α] : Type :=
{μ : measure α // probability_measure μ}

instance probability_measures.coe (α : Type*) [measurable_space α] :
  has_coe (probability_measures α) (measure_theory.measure α) := ⟨subtype.val⟩

@[simp] lemma probability_measures.val_eq_coe {α : Type*} [measurable_space α]
  (ν : probability_measures α) : ν.val = ν := rfl

abbreviation probability_measures.test_against {α : Type*}
  [measurable_space α] [topological_space α] [borel_space α]
  (μ : probability_measures α) (f : bounded_continuous_to_ennreal α) : ennreal :=
lintegral (μ : measure_theory.measure α) f

/-- When `α` is a topological space equipped with its Borel sigma algebra, we introduce the
topology of weak convergence on `probability_measures α`. In some contexts this definition could be
called the weak-* topology. -/
/- The topology of weak convergence on `probability_measures α` is defined as the induced topology
of the mapping  `probability_measures α → ((cont_bdd_ennval α) → ennreal)` to functionals defined
by integration of a test functio against to the measure. -/
instance {α : Type} [measurable_space α] [topological_space α] [borel_space α] :
  topological_space (probability_measures α) :=
topological_space.induced (λ (μ : probability_measures α), probability_measures.test_against μ)
  infer_instance

/- Integration of test functions against borel probability measures depends continuously on the
measure. -/
lemma probability_measures.continuous_test_against {α : Type}
  [measurable_space α] [topological_space α] [borel_space α] :
  continuous (@probability_measures.test_against α _ _ _) := continuous_induced_dom

def finite_measures (α : Type*) [measurable_space α] : Type
  := { μ : measure α // finite_measure μ }

instance finite_measures.coe (α : Type*) [measurable_space α] :
  has_coe (finite_measures α) (measure_theory.measure α) := ⟨subtype.val⟩

@[simp] lemma val_eq_coe_finite_measures {α : Type*} [measurable_space α] (ν : finite_measures α) :
  ν.val = ν := rfl

instance probability_measures.coe_to_finite_measures (α : Type*) [measurable_space α] :
  has_coe (probability_measures α) (finite_measures α) :=
{ coe := λ μ , { val := μ.val ,
                 property := ⟨ by simp [μ.prop.measure_univ] ⟩ , }}

@[simp] lemma val_eq_coe_coe_probability_measures {α : Type*} [measurable_space α]
  (ν : probability_measures α) : ν.val = (ν : finite_measures α) := rfl

abbreviation finite_measures.test_against {α : Type*}
  [measurable_space α] [topological_space α] [borel_space α]
  (μ : finite_measures α) (f : bounded_continuous_to_ennreal α) : ennreal :=
lintegral (μ : measure_theory.measure α) f

lemma probability_measures.test_against_comp_via_finite_measures (α : Type*)
  [measurable_space α] [topological_space α] [borel_space α] :
  @probability_measures.test_against α _ _ _ = (@finite_measures.test_against α _ _ _) ∘ coe :=
by { funext μ f, refl, }

instance {α : Type} [measurable_space α] [topological_space α] [borel_space α] :
  topological_space (finite_measures α) :=
topological_space.induced (λ (μ : finite_measures α), finite_measures.test_against μ)
  infer_instance

lemma finite_measures.continuous_test_against {α : Type}
  [measurable_space α] [topological_space α] [borel_space α] :
  continuous (@finite_measures.test_against α _ _ _) := continuous_induced_dom

lemma probability_measures.coe_embedding (α : Type*)
  [measurable_space α] [topological_space α] [borel_space α] :
  embedding (coe : probability_measures α → finite_measures α) :=
{ induced := begin
    have factorize := probability_measures.test_against_comp_via_finite_measures α,
    have key := @induced_compose (probability_measures α) (finite_measures α)
      (functional_on_bounded_continuous_to_ennreal α) infer_instance coe
      (@finite_measures.test_against α infer_instance infer_instance infer_instance),
    rw ←factorize at key,
    exact key.symm,
  end,
  inj := begin
    intros μ ν h,
    apply subtype.eq ,
    rw [val_eq_coe_coe_probability_measures μ,
        val_eq_coe_coe_probability_measures ν],
    exact congr_arg coe h,
  end, }

lemma proba_meas_tendsto_nhds_iff_fin_meas_tendsto_nhds {α δ : Type*}
  [measurable_space α] [topological_space α] [borel_space α] (F : filter δ)
  {μs : δ → probability_measures α} {μ₀ : probability_measures α} :
  tendsto μs F (𝓝 μ₀) ↔ tendsto (coe ∘ μs) F (𝓝 (μ₀ : finite_measures α)) :=
embedding.tendsto_nhds_iff (probability_measures.coe_embedding α)

theorem finite_measures.weak_conv_seq_iff_test_against {α : Type*}
  [measurable_space α] [topological_space α] [borel_space α]
  {μseq : ℕ → finite_measures α} {μ : finite_measures α} :
  tendsto μseq at_top (𝓝 μ) ↔
  ∀ (f : bounded_continuous_to_ennreal α),
    tendsto (λ n, finite_measures.test_against (μseq(n) : finite_measures α) f) at_top
      (𝓝 (finite_measures.test_against (μ : finite_measures α) f)) :=
begin
  split,
  { intros weak_conv,
    exact tendsto_pi.mp (tendsto.comp (continuous.tendsto
      (@finite_measures.continuous_test_against α _ _ _) μ) weak_conv), },
  { intro h_lim_forall,
    have h_lim : tendsto (λ n, finite_measures.test_against (μseq(n))) at_top
      (𝓝 (finite_measures.test_against μ)),
    by exact tendsto_pi.mpr h_lim_forall,
    rwa [nhds_induced, tendsto_comap_iff], },
end

theorem probability_measures.weak_conv_seq_iff_test_against {α : Type*}
  [measurable_space α] [topological_space α] [borel_space α]
  {μseq : ℕ → probability_measures α} {μ : probability_measures α} :
  tendsto μseq at_top (𝓝 μ) ↔
  ∀ (f : bounded_continuous_to_ennreal α),
    tendsto (λ n, probability_measures.test_against (μseq(n) : probability_measures α) f) at_top
      (𝓝 (probability_measures.test_against (μ : probability_measures α) f)) :=
by rw [@proba_meas_tendsto_nhds_iff_fin_meas_tendsto_nhds α _ _ _ _ at_top μseq μ,
      finite_measures.weak_conv_seq_iff_test_against,
      probability_measures.test_against_comp_via_finite_measures]

/-- The usual definition of weak convergence of probability measures is given in terms of sequences
of probability measures: it is the requirement that the integrals of all continuous bounded
functions against members of the sequence converge. This characterization is shown by
`weak_conv_seq_iff'` in the case when the functions are `ennreal`-valued and the integral is
`lintegral`. -/
/- The most common formulation with `ℝ`-valued functions and Bochner integrals is going to
be `weak_conv_seq_iff`. -/
theorem weak_conv_seq_iff' {α : Type*} [measurable_space α] [topological_space α] [borel_space α]
  {μseq : ℕ → probability_measures α} {μ : probability_measures α} :
  tendsto μseq at_top (𝓝 μ) ↔
  ∀ (f : α → ennreal), continuous f → bounded_above f →
    tendsto (λ n, lintegral (μseq(n) : measure_theory.measure α) f) at_top
      (𝓝 (lintegral (μ : measure_theory.measure α) f)) :=
begin
  rw @probability_measures.weak_conv_seq_iff_test_against α _ _ _ μseq μ,
  split,
  { intros h f f_cont f_bdd,
    exact h (bounded_continuous_to_ennreal.mk' f f_cont f_bdd) , },
  { intros h f,
    exact h f (continuous_of_bounded_continuous_to_ennreal f) (f.bounded_above'), },
end

end topology_of_weak_convergence

end weak_convergence
