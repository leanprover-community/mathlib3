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
* Define the topologies (the current version only defines the types) via
  `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`.
* Prove that an equivalent definition of the topologies is obtained using bounded continuous
  `ℝ`-valued functions instead.
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the types `finite_measure α` and `probability_measure α`.

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
`finite_measure α` to `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`, inheriting the topology from there.

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

namespace measure_theory

section finite_measure
/-!
### Finite measures
In this section, we define the `Type` of finite measures on a given measurable space. This type
will be equipped with the topology of weak convergence of measures when the measurable space is
a topological space equipped with its Borel sigma-algebra.
-/

variables {α : Type*} [measurable_space α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def finite_measure (α : Type*) [measurable_space α] : Type* :=
{ μ : measure α // is_finite_measure μ }

namespace finite_measure

instance has_zero : has_zero (finite_measure α) :=
{ zero := ⟨0, measure_theory.is_finite_measure_zero⟩ }

instance : inhabited (finite_measure α) := { default := 0 }

-- TODO: A coercion `finite_measure α → measure α` is crucial. Now it is the subtype coercion.
-- Another alternative is to use a bijection with `vector_measure α ℝ≥0` as an intermediate step.
-- Potential advantages of the vector measure alternative:
--  * Structures of additive commutative monoid and ℝ≥0 module on `finite_measure α` could be
--    "inherited".
-- Potential drawbacks of the vector measure alternative:
--  * No integration theory directly.
--  * Monotonicity lost as non-measurable sets defined to have measure 0.

/-- A finite measure can be interpreted as a measure. -/
instance : has_coe (finite_measure α) (measure_theory.measure α) := coe_subtype

instance to_measure.is_finite_measure (μ : finite_measure α) :
  is_finite_measure (μ : measure α) := μ.prop

instance : has_add (finite_measure α) :=
{ add := (λ μ ν, ⟨μ + ν, measure_theory.is_finite_measure_add⟩) }

instance : has_scalar ℝ≥0 (finite_measure α) :=
{ smul := (λ (c : ℝ≥0) μ, ⟨c • μ, measure_theory.is_finite_measure_smul_nnreal⟩), }

instance : has_coe_to_fun (finite_measure α) :=
⟨λ _, set α → ℝ≥0, λ μ s, (μ s).to_nnreal⟩

lemma to_fun_eq_to_measure_to_nnreal' (ν : finite_measure α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

lemma to_fun_eq_to_measure_to_nnreal (ν : finite_measure α) (s : set α) :
  ν s = ((ν : measure α) s).to_nnreal := rfl

lemma to_measure_eq_val (ν : finite_measure α) : (ν : measure α) = ν.val := rfl

lemma coe_injective :
  function.injective (coe : finite_measure α → measure α) :=
subtype.coe_injective

@[simp]
lemma coe_zero : (coe : finite_measure α → measure α) 0 = 0 := rfl

@[simp] lemma coe_add (μ ν : finite_measure α) : ↑(μ + ν) = (↑μ + ↑ν : measure α) := rfl

@[simp] lemma coe_smul (c : ℝ≥0) (μ : finite_measure α) : ↑(c • μ) = (c • ↑μ : measure α) := rfl

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : finite_measure α) : ℝ≥0 := μ univ

@[simp] lemma mass_ennreal {μ : finite_measure α} :
  (μ.mass : ℝ≥0∞) = (μ : measure α) univ :=
begin
  apply ennreal.coe_to_nnreal,
  exact ennreal.lt_top_iff_ne_top.mp (μ.prop).measure_univ_lt_top,
end

-- TODO: Another alternative would use a bijection with `vector_measure α ℝ≥0`.
instance : add_comm_monoid (finite_measure α) :=
(finite_measure.coe_injective).add_comm_monoid
  (coe : finite_measure α → measure α) finite_measure.coe_zero finite_measure.coe_add

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure α →+ measure α :=
{ to_fun := coe, map_zero' := coe_zero, map_add' := coe_add }

-- TODO: Another alternative would use a bijection with `vector_measure α ℝ≥0`.
instance {α : Type*} [measurable_space α] : module ℝ≥0 (finite_measure α) :=
function.injective.module _ coe_add_monoid_hom finite_measure.coe_injective coe_smul

end finite_measure -- end namespace

end finite_measure -- end section

section probability_measure
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
def probability_measure (α : Type) [measurable_space α] : Type :=
{μ : measure α // is_probability_measure μ}

namespace probability_measure

instance [inhabited α] : inhabited (probability_measure α) :=
⟨{ val := measure_theory.measure.dirac (default α),
   property := measure_theory.measure.dirac.is_probability_measure, }⟩

/-- A probability measure can be interpreted as a measure. -/
instance : has_coe (probability_measure α) (measure_theory.measure α) := coe_subtype

instance : has_coe_to_fun (probability_measure α) :=
⟨λ _, set α → ℝ≥0, λ μ s, (μ s).to_nnreal⟩

instance to_measure.is_probability_measure (μ : probability_measure α) :
  is_probability_measure (μ : measure α) := μ.prop

lemma to_fun_eq_to_measure_to_nnreal (ν : probability_measure α) :
  (ν : set α → ℝ≥0) = λ s, ((ν : measure α) s).to_nnreal := rfl

@[simp] lemma val_eq_to_measure (ν : probability_measure α) : ν.val = (ν : measure α) := rfl

lemma coe_injective : function.injective (coe : probability_measure α → measure α) :=
subtype.coe_injective

@[simp]
lemma to_fun_univ (ν : probability_measure α) : ν univ = 1 :=
begin
  rw [to_fun_eq_to_measure_to_nnreal, ←ennreal.one_to_nnreal],
  exact congr_arg ennreal.to_nnreal ν.prop.measure_univ,
end

instance has_coe_to_finite_measure : has_coe (probability_measure α) (finite_measure α) :=
{ coe := λ μ , ⟨μ, infer_instance⟩ }

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measure α) : (finite_measure α) := μ

@[simp]
lemma to_finite_measure_coe_eq_coe (ν : probability_measure α) :
  (ν.to_finite_measure : measure α) = (ν : measure α) := rfl

lemma to_finite_measure_coe_eq_val (ν : probability_measure α) :
  (ν.to_finite_measure : measure α) = ν.val := rfl

@[simp]
lemma to_finite_measure_to_fun_eq_to_fun (ν : probability_measure α) :
  (ν.to_finite_measure : set α → ℝ≥0) = (ν : set α → ℝ≥0) := rfl

@[simp]
lemma to_finite_measure_mass (μ : probability_measure α) :
  μ.to_finite_measure.mass = 1 :=
begin
  unfold finite_measure.mass,
  rw [←μ.to_fun_univ, to_finite_measure_to_fun_eq_to_fun],
end

end probability_measure -- end namespace

end probability_measure -- end section

end measure_theory
