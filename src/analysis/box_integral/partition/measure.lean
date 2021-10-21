/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.additive
import measure_theory.measure.lebesgue

/-!
# Box-additive functions defined by measures

In this file we prove a few simple facts about rectangular boxes, partitions, and measures:

- given a box `I : box ι`, its coercion to `set (ι → ℝ)` and `I.Icc` are measurable sets;
- if `μ` is a locally finite measure, then `(I : set (ι → ℝ))` and `I.Icc` have finite measure;
- if `μ` is a locally finite measure, then `λ J, (μ J).to_real` is a box additive function.

For the last statement, we both prove it as a proposition and define a bundled
`box_integral.box_additive` function.

### Tags

rectangular box, measure
-/

open set
noncomputable theory
open_locale ennreal big_operators classical box_integral

variables {ι : Type*}

namespace box_integral

open measure_theory

namespace box

variables (I : box ι)

lemma measurable_set_coe [fintype ι] (I : box ι) : measurable_set (I : set (ι → ℝ)) :=
begin
  rw [coe_eq_pi],
  haveI := fintype.encodable ι,
  exact measurable_set.univ_pi (λ i, measurable_set_Ioc)
end

lemma measurable_set_Icc [fintype ι] (I : box ι) : measurable_set I.Icc := measurable_set_Icc

lemma measure_Icc_lt_top (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] : μ I.Icc < ∞ :=
show μ (Icc I.lower I.upper) < ∞, from (is_compact_pi_Icc I.lower I.upper).measure_lt_top

lemma measure_coe_lt_top (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] : μ I < ∞ :=
(measure_mono $ coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

end box

lemma prepartition.measure_Union_to_real [fintype ι] {I : box ι} (π : prepartition I)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  (μ π.Union).to_real = ∑ J in π.boxes, (μ J).to_real :=
begin
  erw [← ennreal.to_real_sum, π.Union_def, measure_bUnion_finset π.pairwise_disjoint],
  exacts [λ J hJ, J.measurable_set_coe, λ J hJ, (J.measure_coe_lt_top μ).ne]
end

end box_integral

open box_integral box_integral.box

variables [fintype ι]

namespace measure_theory

namespace measure

/-- If `μ` is a locally finite measure on `ℝⁿ`, then `λ J, (μ J).to_real` is a box-additive
function. -/
@[simps] def to_box_additive (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  ι →ᵇᵃ[⊤] ℝ :=
{ to_fun := λ J, (μ J).to_real,
  sum_partition_boxes' := λ J hJ π hπ, by rw [← π.measure_Union_to_real, hπ.Union_eq] }

end measure

end measure_theory

namespace box_integral

open measure_theory

namespace box

@[simp] lemma volume_apply (I : box ι) :
  (volume : measure (ι → ℝ)).to_box_additive I = ∏ i, (I.upper i - I.lower i) :=
by rw [measure.to_box_additive_apply, coe_eq_pi, real.volume_pi_Ioc_to_real I.lower_le_upper]

lemma volume_face_mul {n} (i : fin (n + 1)) (I : box (fin (n + 1))) :
  (∏ j, ((I.face i).upper j - (I.face i).lower j)) * (I.upper i - I.lower i) =
    ∏ j, (I.upper j - I.lower j) :=
by simp only [face_lower, face_upper, (∘), fin.prod_univ_succ_above _ i, mul_comm]

end box

namespace box_additive_map

/-- Box-additive map sending each box `I` to the continuous linear endomorphism
`x ↦ (volume I).to_real • x`. -/
protected def volume {E : Type*} [normed_group E] [normed_space ℝ E] :
  ι →ᵇᵃ (E →L[ℝ] E) :=
(volume : measure (ι → ℝ)).to_box_additive.to_smul

lemma volume_apply {E : Type*} [normed_group E] [normed_space ℝ E] (I : box ι) (x : E) :
  box_additive_map.volume I x = (∏ j, (I.upper j - I.lower j)) • x :=
congr_arg2 (•) I.volume_apply rfl

end box_additive_map

end box_integral
