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

notation `μ_ℝmodℤ`:=measure_theory.measure.add_haar_measure positive_compacts_univ

instance : compact_space ℝmodℤ := sorry

instance : t2_space ℝmodℤ := sorry

--instance : second_countable_topology ℝmodℤ := sorry

variables [measurable_space ℝmodℤ] [borel_space ℝmodℤ]

/-- Move somewhere ??? algebra.floor? -/
lemma RmodZuniqueRep :
∀ (t : ℝ), ∃! (x : ℝ), ∃ (n : ℤ), x ∈ Ico (0:ℝ) 1 ∧ t = x + n :=
begin
  intro t,
  let n := floor t,
  let x := t-n,
  use x,
  use n,
  split,
  { split,
    { dsimp only [x, n],
      have := floor_le t,
      linarith, },
    { dsimp only [x, n],
      have := lt_floor_add_one t,
      linarith, }, },
  { dsimp only [x, n],
    ring, },
  { intros y hy,
    obtain ⟨nn, hny, hnt⟩ := hy,
    have : (nn:ℝ) = floor t,
    { have : (nn:ℝ) ≤ y+nn ∧ y+nn < nn + 1 ,
      { have := hny.1,
        have := hny.2,
        split; linarith, },
      rw [(floor_eq_iff.mpr this).symm, hnt], },
    dsimp only [x, n],
    rw [← this, hnt],
    ring, },
end



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


lemma min_cases {α : Type*} [linear_order α] (a b : α) :
min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a :=
begin
  by_cases a ≤ b,
  { left,
    exact ⟨min_eq_left h, h⟩ },
  { right,
    push_neg at h,
    exact ⟨min_eq_right (le_of_lt h), h⟩ }
end

lemma max_cases {α : Type*} [linear_order α] (a b : α) :
max a b = b ∧ a ≤ b ∨ max a b = a ∧ b < a :=
begin
  by_cases a ≤ b,
  { left,
    exact ⟨max_eq_right h, h⟩ },
  { right,
    push_neg at h,
    exact ⟨max_eq_left (le_of_lt h), h⟩ }
end




/-- Move elsewhere -/
lemma Ico_translate (a b x : ℝ) : has_add.add x ⁻¹' Ico a b = Ico (a-x) (b-x) :=
begin
  -- compare to set.Ico_add_bij  ??? Turn `=` into `bij_on`?? (When image sets are same `Type`??)
  ext1 y,
  split,
  { intros hy,
    simp only [preimage_const_add_Ico, mem_Ico, sub_neg_eq_add] at hy,
    exact mem_Ico.mpr hy, },
  { intros hy,
    simp only [preimage_const_add_Ico, mem_Ico, sub_neg_eq_add],
    exact mem_Ico.mp hy, },
end



lemma something1
--(S : set ℝ ) (hS : measurable_set S)
--(h : S = Ico 0 1)
--(h : ∀ t, ∃! x:ℝ ,  ∃n:ℤ, x∈ S ∧  t=x+n )
:
measure.map (quotient_add_group.mk : (ℝ → ℝmodℤ)) (measure.restrict volume (Ico (0:ℝ) 1)) =
 μ_ℝmodℤ :=
begin
  have meas1 : measurable (quotient_add_group.mk : (ℝ → ℝmodℤ)),
  { apply continuous.measurable,
    exact continuous_quotient_mk, },
  let S := Ico (0:ℝ) 1,
  have Smeas : measurable_set S := measurable_set_Ico,
  haveI : finite_measure (measure.restrict volume (Ico (0:ℝ) 1)) := ⟨by simp⟩,
  haveI : finite_measure (measure.map (quotient_add_group.mk : (ℝ → ℝmodℤ))
    (measure.restrict volume (Ico (0:ℝ) 1))),
  { refine measure_theory.measure.is_finite_measure_map _ _,
    exact meas1, },

  rw @measure_theory.measure.add_haar_measure_unique ℝmodℤ _ _ _ _ _ _ _ _
    (measure.map (quotient_add_group.mk : (ℝ → ℝmodℤ)) (measure.restrict volume S)) _ _
    (positive_compacts_univ),

  { transitivity (1:ennreal) • μ_ℝmodℤ,
    { congr,
      rw measure_theory.measure.map_apply,
      { simp [positive_compacts_univ], },
      { exact meas1, },
      { exact measurable_set.univ, }, },
    { simp, }, },
  { rw ←measure_theory.measure.map_add_left_eq_self,
    intros x,
    ext1 A hA,
    rw [measure_theory.measure.map_apply, measure_theory.measure.map_apply,
      measure_theory.measure.map_apply],

    {


      -- make this `obtain` a lemma for the group theory library! ...
      obtain ⟨x0, hx0⟩ := @quotient.exists_rep _ (quotient_add_group.left_rel genBy1) x,

      obtain ⟨x1, ⟨n, ⟨hx11, hx12⟩ , hn⟩, hx1'⟩ := RmodZuniqueRep x0,

      have xquotx1 : x = quotient_add_group.mk x1,
      { rw ← hx0,
        rw hn,
        refine quotient_add_group.eq.mpr _,
        use -n,
        simp, },
      have is_a_homo : ∀ z y, quotient_add_group.mk (z + y) = quotient_add_group.mk z
        + quotient_add_group.mk y :=
        add_monoid_hom.map_add (quotient_add_group.mk' genBy1),
      have two_quotients : quotient_add_group.mk ⁻¹' (has_add.add x ⁻¹' A) =
        has_add.add x1 ⁻¹' (quotient_add_group.mk ⁻¹' A),
      { ext1 y,
        simp only [mem_preimage],
        rw [xquotx1, is_a_homo x1 y], },
      let A1 := (quotient_add_group.mk ⁻¹' A) ∩ Ico x1 1,
      have A1meas : measurable_set A1 := measurable_set.inter (measurable_set_preimage meas1 hA)
        measurable_set_Ico,
      let A2 := (quotient_add_group.mk ⁻¹' A) ∩ Ico 0 x1,
      have A2meas : measurable_set A2 := measurable_set.inter (measurable_set_preimage meas1 hA)
        measurable_set_Ico,
      have A1A2dis : disjoint A1 A2,
      { dsimp only [A1, A2],
        apply disjoint.inter,
        rw set.Ico_disjoint_Ico,
        cases (min_cases 1 x1); cases (max_cases x1 0); linarith, },
      have A1A2 : (quotient_add_group.mk ⁻¹' A) ∩ Ico 0 1 = A1 ∪ A2,
      { convert set.inter_union_distrib_left using 2,
        rw set.union_comm,
        refine (set.Ico_union_Ico_eq_Ico _ _).symm; linarith, },
      let B1 : set ℝ :=  has_add.add x1 ⁻¹' A1,
      have B1meas : measurable_set B1 := measurable_set_preimage (measurable_const_add _) A1meas,
      let B2 : set ℝ := has_add.add (x1-1) ⁻¹' A2,
      have B2meas : measurable_set B2 := measurable_set_preimage (measurable_const_add _) A2meas,
      have B1B2dis : disjoint B1 B2,
      { have B1sub : B1 ⊆ has_add.add x1 ⁻¹' (Ico x1 1),
        { rw function.surjective.preimage_subset_preimage_iff,
          { exact (quotient_add_group.mk ⁻¹' A).inter_subset_right _, },
          { exact add_left_surjective _, }, },
        have B2sub : B2 ⊆ has_add.add (x1-1) ⁻¹' (Ico 0 x1),
        { rw function.surjective.preimage_subset_preimage_iff,
          { exact (quotient_add_group.mk ⁻¹' A).inter_subset_right _, },
          { exact add_left_surjective _, }, },
        refine set.disjoint_of_subset B1sub B2sub _,
        rw (by convert Ico_translate _ _ x1; ring :
          has_add.add x1 ⁻¹' Ico x1 1 = Ico 0 (1-x1)),
        rw (by convert Ico_translate _ _ (x1-1) using 2; ring :
          has_add.add (x1-1) ⁻¹' Ico 0 x1 = Ico (1-x1) 1),
        rw set.Ico_disjoint_Ico,
        cases (min_cases (1-x1) 1); cases (max_cases 0 (1-x1)); linarith, },
      have B1B2 :  (quotient_add_group.mk ⁻¹' (has_add.add x ⁻¹' A)) ∩ S = B1 ∪ B2,
      { rw two_quotients,
        rw (by rw set.Ico_union_Ico_eq_Ico; linarith : S = Ico 0 (1-x1) ∪ (Ico (1-x1) 1)),
        rw set.inter_distrib_left,

        have B1is : has_add.add x1 ⁻¹' (quotient_add_group.mk ⁻¹' A) ∩ Ico 0 (1 - x1) = B1 :=
          by rw [← (by convert Ico_translate _ _ x1; ring :
            has_add.add x1 ⁻¹' Ico x1 1 = Ico 0 (1-x1)), ← set.preimage_inter],
        have B2is : has_add.add x1 ⁻¹' (quotient_add_group.mk ⁻¹' A) ∩ Ico (1 - x1) 1 = B2,
        {
          rw [(_ : has_add.add x1 ⁻¹' (quotient_add_group.mk ⁻¹' A)
            = has_add.add (x1-1) ⁻¹' (quotient_add_group.mk ⁻¹' A) ),
            ←(by convert Ico_translate _ _ (x1-1) using 2; ring :
            has_add.add (x1-1) ⁻¹' Ico 0 x1 = Ico (1-x1) 1),
             ← set.preimage_inter],

          have : has_add.add (x1 - 1) ⁻¹' (quotient_add_group.mk ⁻¹' A) =
            has_add.add x1 ⁻¹' (has_add.add (-1) ⁻¹' (quotient_add_group.mk ⁻¹' A)),
          { conv_rhs {rw ← set.preimage_comp,},
            rw [comp_add_left, add_comm, sub_eq_add_neg], },
          rw this,

          congr' 1,
          { ext1 y,
            simp only [mem_preimage],
            rw is_a_homo,
            have : @quotient_add_group.mk _ _ genBy1 (-1:ℝ) = 0,
            { refine (quotient_add_group.eq_zero_iff (-1:ℝ)).mpr _,
              simp, },
            rw [this, zero_add], }, },

        exact congr_arg2 (λ (a c : set ℝ), a ∪ c) B1is B2is, },
      rw [measure_theory.measure.restrict_apply', measure_theory.measure.restrict_apply'],
      { rw [A1A2,
          B1B2],
        rw [measure_theory.measure_union, measure_theory.measure_union,
          real.volume_preimage_add_left, real.volume_preimage_add_left],
        { exact A1A2dis, },
        { exact A1meas, },
        { exact A2meas, },
        { exact B1B2dis, },
        { exact B1meas, },
        { exact B2meas, }, },
      { exact Smeas, },
      { exact Smeas, },
    },
    { exact meas1, },
    { exact hA, },
    { exact meas1, },
    { refine measurable_set_preimage (measurable_const_add _) hA, },
    { refine measurable_const_add _, },
    { exact hA, }, },
end
