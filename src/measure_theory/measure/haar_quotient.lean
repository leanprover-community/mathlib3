/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.measure.lebesgue

/-!
# Haar Quotient measure

In this file does stuff.

## Main Declarations

* `haar_measure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.

## References
* Paul Halmos (1950), Measure Theory, §53
-/

open set measure_theory

notation `genBy1` := add_subgroup.gmultiples (1:ℝ)

notation `ℝmodℤ` := quotient_add_group.quotient genBy1

notation `μ_ℝmodℤ` := measure_theory.measure.add_haar_measure
  (topological_space.positive_compacts_univ : topological_space.positive_compacts ℝmodℤ)

instance : compact_space ℝmodℤ := sorry

instance : t2_space ℝmodℤ :=
{ t2 := begin
  intros x y hxy,
  sorry,
end }

instance : separated_space (metric.sphere (0:ℝ) 1) := to_separated

instance : topological_space.second_countable_topology ℝmodℤ := sorry

variables [measurable_space ℝmodℤ] [borel_space ℝmodℤ]

theorem disjoint.inter {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (u ∩ s) (u ∩ t) :=
begin
  apply disjoint.inter_right',
  apply disjoint.inter_left',
  exact h,
end

theorem disjoint.inter' {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (s ∩ u) (t ∩ u) :=
begin
  apply disjoint.inter_left,
  apply disjoint.inter_right,
  exact h,
end

noncomputable def int.fract (a : ℝ) : ℝ := a - floor a

theorem int.fract_nonneg (a : ℝ) :
0 ≤ int.fract a := sorry

theorem int.fract_lt_one (a : ℝ) :
int.fract a < 1 := sorry

lemma min_cases {α : Type*} [linear_order α] (a b : α) :
min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := sorry

lemma max_cases {α : Type*} [linear_order α] (a b : α) :
max a b = b ∧ a ≤ b ∨ max a b = a ∧ b < a := sorry


lemma map_restrict_unit_interval :
  measure.map (quotient_add_group.mk' genBy1) (volume.restrict (Ico 0 1)) = μ_ℝmodℤ :=
begin
  let S := Ico (0:ℝ) 1,
  let π : ℝ →+ ℝmodℤ := quotient_add_group.mk' genBy1,
  have π_of_ℤ : ∀ z:ℤ, π z = 0 := λ z, (quotient_add_group.eq_zero_iff (z:ℝ)).mpr ⟨z, by simp⟩,
  have meas_π : measurable π :=
    continuous.measurable continuous_quotient_mk, -- projection notation doesn't work here?
  have Smeas : measurable_set S := measurable_set_Ico,
  haveI : is_finite_measure (volume.restrict S) := ⟨by simp⟩,
  haveI : is_finite_measure (measure.map π
    (volume.restrict S)) := measure_theory.measure.is_finite_measure_map _ meas_π,
  -- to show that a measure is Haar, enough to show left invariance
  suffices : is_add_left_invariant (measure.map π (volume.restrict S)),
  { rw @measure_theory.measure.add_haar_measure_unique ℝmodℤ _ _ _ _ _ _ _
      (measure.map π (volume.restrict S)) _ this
      (topological_space.positive_compacts_univ),
    { transitivity (1:ennreal) • μ_ℝmodℤ,
    { congr,
      rw measure_theory.measure.map_apply meas_π,
      { simp [topological_space.positive_compacts_univ], },
      { exact measurable_set.univ, }, },
    { simp, }, }, },
  rw ←measure_theory.measure.map_add_left_eq_self,
  intros x,
  ext1 A hA,
  rw [measure_theory.measure.map_apply meas_π hA,
    measure_theory.measure.map_apply (measurable_const_add _) hA,
    measure_theory.measure.map_apply meas_π
    (measurable_set_preimage (measurable_const_add _) hA)],
  -- given A ⊂ ℝ/ℤ and x ∈ ℝ/ℤ, need that μ(A∩S)=μ((-x+A)∩S)
  -- step1: get x1 ∈ S with π(x1)=x
  obtain ⟨x1, ⟨hx11, hx12⟩, xquotx1⟩ : ∃ x1, x1 ∈ S ∧ x = π x1,
  { obtain ⟨x0, (hx0 : π x0 = x)⟩ := @quotient.exists_rep _ (quotient_add_group.left_rel genBy1) x,
    refine ⟨int.fract x0, ⟨int.fract_nonneg _, int.fract_lt_one _⟩,
      by simp [int.fract, hx0, π_of_ℤ (⌊x0⌋)]⟩, },
  set π_preA := π ⁻¹' A,
  set π_prexA := π ⁻¹' (has_add.add x ⁻¹' A),
  have two_quotients : π_prexA = has_add.add x1 ⁻¹' π_preA,
  { ext1 y,
    simp [xquotx1], },
  -- take the subinterval of π_preA in [x1,1)
  let A1 := π_preA ∩ Ico x1 1,
  have A1meas : measurable_set A1 := measurable_set.inter (measurable_set_preimage meas_π hA)
    measurable_set_Ico,
  -- and the rest is in [0,x1)
  let A2 := π_preA ∩ Ico 0 x1,
  have A2meas : measurable_set A2 := measurable_set.inter (measurable_set_preimage meas_π hA)
    measurable_set_Ico,
  have A1A2dis : disjoint A1 A2,
  { apply disjoint.inter,
    rw Ico_disjoint_Ico,
    cases (min_cases 1 x1); cases (max_cases x1 0); linarith, },
  have A1A2 : π_preA ∩ S = A1 ∪ A2,
  { convert inter_union_distrib_left using 2,
    rw union_comm,
    refine (Ico_union_Ico_eq_Ico _ _).symm; linarith, },
  -- under (-x1), A1 is moved into [0,1-x1)
  let B1 : set ℝ :=  has_add.add x1 ⁻¹' A1,
  have B1meas : measurable_set B1 := measurable_set_preimage (measurable_const_add _) A1meas,
  -- and A2 is moved into [1-x1,1), up to translation by 1
  let B2 : set ℝ := has_add.add (x1-1) ⁻¹' A2,
  have B2meas : measurable_set B2 := measurable_set_preimage (measurable_const_add _) A2meas,
  have B1B2dis : disjoint B1 B2,
  { have B1sub : B1 ⊆ has_add.add x1 ⁻¹' (Ico x1 1) :=
      preimage_mono (π_preA.inter_subset_right _),
    have B2sub : B2 ⊆ has_add.add (x1-1) ⁻¹' (Ico 0 x1) :=
      preimage_mono (π_preA.inter_subset_right _),
    refine disjoint_of_subset B1sub B2sub _,
    rw [preimage_const_add_Ico, preimage_const_add_Ico, Ico_disjoint_Ico],
    cases min_cases (1-x1) (x1 - (x1 - 1)); cases max_cases (x1 - x1) (0 - (x1 - 1)); linarith, },
  have B1B2 : π_prexA ∩ S = B1 ∪ B2,
  { have B1is : has_add.add x1 ⁻¹' π_preA ∩ Ico 0 (1 - x1) = B1 :=
      by simp [B1],
    have B2is : has_add.add x1 ⁻¹' π_preA ∩ Ico (1 - x1) 1 = B2,
    { calc has_add.add x1 ⁻¹' π_preA ∩ Ico (1 - x1) 1
          = has_add.add (x1 - 1) ⁻¹' π_preA ∩ Ico (1 - x1) 1 : _
      ... = B2 : by simp [B2],
      congr' 1,
      ext1 y,
      have : π 1 = 0 := by simpa using π_of_ℤ 1,
      simp [this], },
    have : S = Ico 0 (1-x1) ∪ (Ico (1-x1) 1) := by rw Ico_union_Ico_eq_Ico; linarith,
    rw [two_quotients, this, inter_distrib_left, B1is, B2is], },
  rw [measure_theory.measure.restrict_apply' Smeas,
    measure_theory.measure.restrict_apply' Smeas,
    A1A2, B1B2, measure_theory.measure_union B1B2dis B1meas B2meas,
    measure_theory.measure_union A1A2dis A1meas A2meas,
    real.volume_preimage_add_left, real.volume_preimage_add_left],
end
