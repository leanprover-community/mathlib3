/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.measure.measure_space

/-!
# Weak convergence of (finite) measures

This file will define the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f` on, the integration of `f` against the
measure is continuous.

TODOs:
* Rename the types `finite_measures α` -> `finite_measure α` and
  `probability_measures α` -> `probability_measure α` after PR #8831.
* Define the topologies (the current version only defines the types) via
  `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`.
* Prove that and equivalent definition of the topologies is obtained using bounded continuous
  `ℝ`-valued functions.
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the types `finite_measures α` and `probability_measures α`.

TODO:
* Define the topologies on the above types.

## Main results

None yet.

TODO:
* Portmanteau theorem.

## Notations

No new notation is introduced.

## Implementation notes

The topology of weak convergence of finite Borel measures will be defined using a mapping from
`finite_measures α` to `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`, inheriting the topology from there.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure, probability measure

-/

noncomputable theory
open measure_theory
open set
open filter
open_locale topological_space ennreal nnreal

section finite_measures
/-!
### Finite measures
In this section, we define the `Type` of finite measures on a given measurable space. This type
will be equipped with the topology of weak convergence of measures when the measurable space is
a topological space equipped with its Borel sigma-algebra.
-/

variables {α : Type} [measurable_space α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def finite_measures (α : Type*) [measurable_space α] : Type :=
{ μ : measure α // finite_measure μ }

namespace finite_measures

instance has_zero {α : Type*} [measurable_space α] :
  has_zero (finite_measures α) :=
⟨{ val := 0,
   property := measure_theory.finite_measure_zero, }⟩

instance : inhabited (finite_measures α) := { default := 0 }

instance {α : Type*} [measurable_space α] : has_add (finite_measures α) :=
{ add := (λ (μ ν : finite_measures α),
  { val := μ.val + ν.val,
    property := @measure_theory.finite_measure_add α _ μ.val ν.val μ.prop ν.prop, }), }

instance {α : Type*} [measurable_space α] : has_scalar ℝ≥0 (finite_measures α) :=
{ smul := (λ (c : ℝ≥0) (μ : finite_measures α),
  { val := c • μ.val,
    property := @measure_theory.finite_measure_smul_nnreal α _ μ.val μ.prop c, }), }

-- TODO: A coercion `finite_measures α → measure α` is crucial. Now it is the subtype coercion.
-- Another alternative is to use a bijection with `vector_measure α ℝ≥0` as an intermediate step.
-- Potential advantages of the vector measure alternative:
--  * Structures of additive commutative monoid and ℝ≥0 module on `finite_measure α` could be
--    "inherited".
-- Potential drawbacks of the vector measure alternative:
--  * No integration theory directly.
--  * Monotonicity lost as non-measurable sets defined to have measure 0.

/-- A finite measure can be interpreted as a measure. -/
instance : has_coe (finite_measures α) (measure_theory.measure α) := coe_subtype

instance to_measure.finite_measure (μ : finite_measures α) :
  finite_measure (μ : measure α) := μ.prop

instance (α : Type*) [measurable_space α] :
  has_coe_to_fun (finite_measures α) := ⟨(λ _, set α → ℝ≥0),
    (λ μ, (λ s, (μ.val.measure_of s).to_nnreal))⟩

lemma to_fun_eq_to_measure_to_nnreal (ν : finite_measures α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

lemma to_measure_eq_val (ν : finite_measures α) : (ν : measure α) = ν.val := rfl

lemma coe_injective :
  function.injective (coe : finite_measures α → measure α) :=
by { intros μ ν, exact subtype.eq, }

@[simp]
lemma coe_zero : (coe : finite_measures α → measure α) 0 = 0 := rfl

@[simp]
lemma coe_add (μ ν : finite_measures α) :
  (coe : finite_measures α → measure α) (μ + ν) = (μ : measure α) + (ν : measure α) := rfl

@[simp]
lemma coe_smul (c : ℝ≥0) (μ : finite_measures α) :
  (coe : finite_measures α → measure α) (c • μ)  = c • (μ : measure α) := rfl

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass {α : Type*} [measurable_space α] (μ : finite_measures α) : ℝ≥0 := μ univ

lemma mass_def {α : Type*} [measurable_space α] {μ : finite_measures α} :
  μ.mass = μ univ := rfl

@[simp] lemma mass_ennreal {α : Type*} [measurable_space α]
  {μ : finite_measures α} : (μ.mass : ℝ≥0∞) = (μ : measure α) univ :=
begin
  apply ennreal.coe_to_nnreal,
  exact ennreal.lt_top_iff_ne_top.mp (μ.prop).measure_univ_lt_top,
end

-- TODO: Another alternative would use a bijection with `vector_measure α ℝ≥0`.
instance {α : Type*} [measurable_space α] :
  add_comm_monoid (finite_measures α) :=
(finite_measures.coe_injective).add_comm_monoid
  (coe : finite_measures α → measure α) finite_measures.coe_zero finite_measures.coe_add

#check @finite_measures.has_scalar α _

-- TODO: Another alternative would use a bijection with `vector_measure α ℝ≥0`.
instance {α : Type*} [measurable_space α] :
  module ℝ≥0 (finite_measures α) :=
{ smul := (@finite_measures.has_scalar α _).smul,
  one_smul := begin
    intros μ,
    apply finite_measures.coe_injective,
    simp only [coe_smul, one_smul],
  end,
  mul_smul := begin
    intros c₁ c₂ μ,
    apply finite_measures.coe_injective,
    simp only [coe_smul, mul_smul],
  end,
  smul_add := begin
    intros c μ ν,
    apply finite_measures.coe_injective,
    simp only [coe_add, coe_smul, smul_add],
  end,
  smul_zero := begin
    intros c,
    apply finite_measures.coe_injective,
    simp only [coe_smul, coe_zero, smul_zero],
  end,
  add_smul := begin
    intros c₁ c₂ μ,
    apply finite_measures.coe_injective,
    simp only [add_smul, coe_add, coe_smul],
  end,
  zero_smul := begin
    intros μ,
    apply finite_measures.coe_injective,
    simp only [coe_smul, zero_smul, coe_zero],
  end }

end finite_measures -- end namespace

end finite_measures -- end section



section probability_measures
/-!
### Probability measures
In this section, we define the `Type` of probability measures on a given measurable space. This
type will be equipped with the topology of weak convergence of measures when the measurable space
is a topological space equipped with its Borel sigma-algebra.

There is a coercion (embedding) to finite measures on the same space.
-/

variables {α : Type} [measurable_space α]

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measures (α : Type) [measurable_space α] : Type :=
{μ : measure α // probability_measure μ}

namespace probability_measures

instance [inhabited α] : inhabited (probability_measures α) :=
⟨{ val := measure_theory.measure.dirac (default α),
   property := measure_theory.measure.dirac.probability_measure, }⟩

/-- A probability measure can be interpreted as a measure. -/
instance : has_coe (probability_measures α) (measure_theory.measure α) := coe_subtype

instance (α : Type*) [measurable_space α] :
  has_coe_to_fun (probability_measures α) := ⟨(λ _, set α → ℝ≥0),
    (λ μ, (λ s, (μ.val.measure_of s).to_nnreal))⟩

instance to_measure.probability_measure (μ : probability_measures α) :
  probability_measure (μ : measure α) := μ.prop

lemma to_fun_eq_to_measure_to_nnreal (ν : probability_measures α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

lemma to_measure_eq_val (ν : probability_measures α) : (ν : measure α) = ν.val := rfl

lemma coe_injective :
  function.injective (coe : probability_measures α → measure α) :=
by { intros μ ν, exact subtype.eq, }

@[simp]
lemma to_fun_univ (ν : probability_measures α) : ν univ = 1 :=
begin
  rw [to_fun_eq_to_measure_to_nnreal, ←ennreal.one_to_nnreal],
  exact congr_arg ennreal.to_nnreal ν.prop.measure_univ,
end

instance has_coe_to_finite_measures (α : Type*) [measurable_space α] :
  has_coe (probability_measures α) (finite_measures α) :=
{ coe := λ μ , { val := μ.val,
                 property := begin
                   have key : (1 : ennreal) < ⊤ := ennreal.one_lt_top,
                   rw [←μ.prop.measure_univ] at key,
                   exact ⟨key⟩,
                 end, }}

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measures α) : (finite_measures α) := μ

@[simp]
lemma to_finite_measure_coe_eq_coe (ν : probability_measures α) :
  (ν.to_finite_measure : measure α) = (ν : measure α) := rfl

lemma to_finite_measure_coe_eq_val (ν : probability_measures α) :
  (ν.to_finite_measure : measure α) = ν.val := rfl

@[simp]
lemma to_finite_measure_to_fun_eq_to_fun (ν : probability_measures α) :
  (ν.to_finite_measure : set α → ℝ≥0) = (ν : set α → ℝ≥0) := rfl

@[simp]
lemma to_finite_measure_mass (μ : probability_measures α) :
  μ.to_finite_measure.mass = 1 :=
begin
  unfold finite_measures.mass,
  rw [←μ.to_fun_univ, to_finite_measure_to_fun_eq_to_fun],
end

end probability_measures -- end namespace

end probability_measures -- end section
