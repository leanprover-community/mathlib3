/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.borel_space
/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: left and right invariant measures
* We define the conjugate `A ↦ μ (A⁻¹)` of a measure `μ`, and show that it is right invariant iff
  `μ` is left invariant
-/
noncomputable theory

open has_inv set function

namespace measure_theory

variables {G : Type*}

section

variables [measurable_space G] [has_mul G]

/-- A measure `μ` on a topological group is left invariant if
  for all measurable sets `s` and all `g`, we have `μ (gs) = μ s`,
  where `gs` denotes the translate of `s` by left multiplication with `g`. -/
def is_left_invariant (μ : set G → ennreal) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, g * h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant if
  for all measurable sets `s` and all `g`, we have `μ (sg) = μ s`,
  where `sg` denotes the translate of `s` by right multiplication with `g`. -/
def is_right_invariant (μ : set G → ennreal) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, h * g) ⁻¹' A) = μ A

end

namespace measure

variables [measurable_space G]

lemma map_mul_left_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} : (∀ g, measure.map ((*) g) μ = μ) ↔ is_left_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_left g) hA]
end

lemma map_mul_right_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} : (∀ g, measure.map (λ h, h * g) μ = μ) ↔ is_right_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_right g) hA]
end

/-- The conjugate of a measure on a topological group.
  Defined to be `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
protected def conj [group G] (μ : measure G) : measure G :=
measure.map inv μ

variables [group G] [topological_space G] [topological_group G] [borel_space G]

lemma conj_apply (μ : measure G) {s : set G} (hs : is_measurable s) :
  μ.conj s = μ s⁻¹ :=
by { unfold measure.conj, rw [measure.map_apply measurable_inv hs, inv_preimage] }

@[simp] lemma conj_conj (μ : measure G) : μ.conj.conj = μ :=
begin
  ext1 s hs, rw [μ.conj.conj_apply hs, μ.conj_apply, set.inv_inv], exact measurable_inv hs
end

variables {μ : measure G}

lemma regular.conj [t2_space G] (hμ : μ.regular) : μ.conj.regular :=
hμ.map (homeomorph.inv G)

end measure

section conj
variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]
  {μ : measure G}

@[simp] lemma regular_conj_iff [t2_space G] : μ.conj.regular ↔ μ.regular :=
by { refine ⟨λ h, _, measure.regular.conj⟩, rw ←μ.conj_conj, exact measure.regular.conj h }

lemma is_right_invariant_conj' (h : is_left_invariant μ) :
  is_right_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_right g hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr, intro h, simp only [mul_inv_rev, comp_app, inv_inv]
end

lemma is_left_invariant_conj' (h : is_right_invariant μ) : is_left_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_left g hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr, intro h, simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp] lemma is_right_invariant_conj : is_right_invariant μ.conj ↔ is_left_invariant μ :=
by { refine ⟨λ h, _, is_right_invariant_conj'⟩, rw ←μ.conj_conj, exact is_left_invariant_conj' h }

@[simp] lemma is_left_invariant_conj : is_left_invariant μ.conj ↔ is_right_invariant μ :=
by { refine ⟨λ h, _, is_left_invariant_conj'⟩, rw ←μ.conj_conj, exact is_right_invariant_conj' h }

end conj

end measure_theory
