/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.integral.set_integral

/-!
# Integral average of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `measure_theory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `measure_theory.integrable.to_average`.

## Tags

integral, center mass, average value
-/

open measure_theory measure_theory.measure metric set filter topological_space function
open_locale topology big_operators ennreal convex

variables {α E F : Type*} {m0 : measurable_space α}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {μ : measure α} {s : set E}

/-!
### Average value of a function w.r.t. a measure

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`) is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

-/

namespace measure_theory

variable (μ)
include m0

/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍ x, f x ∂μ`. It is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

For the average on a set, use `⨍ x in s, f x ∂μ` (defined as `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) := ∫ x, f x ∂((μ univ)⁻¹ • μ)

notation `⨍` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := average μ r
notation `⨍` binders `, ` r:(scoped:60 f, average volume f) := r
notation `⨍` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 := average (measure.restrict μ s) r
notation `⨍` binders ` in ` s `, ` r:(scoped:60 f, average (measure.restrict volume s) f) := r

@[simp] lemma average_zero : ⨍ x, (0 : E) ∂μ = 0 := by rw [average, integral_zero]

@[simp] lemma average_zero_measure (f : α → E) : ⨍ x, f x ∂(0 : measure α) = 0 :=
by rw [average, smul_zero, integral_zero_measure]

@[simp] lemma average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ := integral_neg f

lemma average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂((μ univ)⁻¹ • μ) := rfl

lemma average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ univ).to_real⁻¹ • ∫ x, f x ∂μ :=
by rw [average_eq', integral_smul_measure, ennreal.to_real_inv]

lemma average_eq_integral [is_probability_measure μ] (f : α → E) :
  ⨍ x, f x ∂μ = ∫ x, f x ∂μ :=
by rw [average, measure_univ, inv_one, one_smul]

@[simp] lemma measure_smul_average [is_finite_measure μ] (f : α → E) :
  (μ univ).to_real • ⨍ x, f x ∂μ = ∫ x, f x ∂μ :=
begin
  cases eq_or_ne μ 0 with hμ hμ,
  { rw [hμ, integral_zero_measure, average_zero_measure, smul_zero] },
  { rw [average_eq, smul_inv_smul₀],
    refine (ennreal.to_real_pos _ $ measure_ne_top _ _).ne',
    rwa [ne.def, measure_univ_eq_zero] }
end

lemma set_average_eq (f : α → E) (s : set α) :
  ⨍ x in s, f x ∂μ = (μ s).to_real⁻¹ • ∫ x in s, f x ∂μ :=
by rw [average_eq, restrict_apply_univ]

lemma set_average_eq' (f : α → E) (s : set α) :
  ⨍ x in s, f x ∂μ = ∫ x, f x ∂((μ s)⁻¹ • μ.restrict s) :=
by simp only [average_eq', restrict_apply_univ]

variable {μ}

lemma average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ :=
by simp only [average_eq, integral_congr_ae h]

lemma average_add_measure [is_finite_measure μ] {ν : measure α} [is_finite_measure ν] {f : α → E}
  (hμ : integrable f μ) (hν : integrable f ν) :
  ⨍ x, f x ∂(μ + ν) =
    ((μ univ).to_real / ((μ univ).to_real + (ν univ).to_real)) • ⨍ x, f x ∂μ +
      ((ν univ).to_real / ((μ univ).to_real + (ν univ).to_real)) • ⨍ x, f x ∂ν :=
begin
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν, ← ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top ν _)],
  rw [average_eq, measure.add_apply]
end

lemma average_pair {f : α → E} {g : α → F} (hfi : integrable f μ) (hgi : integrable g μ) :
  ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
integral_pair hfi.to_average hgi.to_average

lemma measure_smul_set_average (f : α → E) {s : set α} (h : μ s ≠ ∞) :
  (μ s).to_real • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ :=
by { haveI := fact.mk h.lt_top, rw [← measure_smul_average, restrict_apply_univ] }

lemma average_union {f : α → E} {s t : set α} (hd : ae_disjoint μ s t)
  (ht : null_measurable_set t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ⨍ x in s ∪ t, f x ∂μ =
    ((μ s).to_real / ((μ s).to_real + (μ t).to_real)) • ⨍ x in s, f x ∂μ +
      ((μ t).to_real / ((μ s).to_real + (μ t).to_real)) • ⨍ x in t, f x ∂μ :=
begin
  haveI := fact.mk hsμ.lt_top, haveI := fact.mk htμ.lt_top,
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, restrict_apply_univ, restrict_apply_univ]
end

lemma average_union_mem_open_segment {f : α → E} {s t : set α} (hd : ae_disjoint μ s t)
  (ht : null_measurable_set t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ⨍ x in s ∪ t, f x ∂μ ∈ open_segment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) :=
begin
  replace hs₀ : 0 < (μ s).to_real, from ennreal.to_real_pos hs₀ hsμ,
  replace ht₀ : 0 < (μ t).to_real, from ennreal.to_real_pos ht₀ htμ,
  refine mem_open_segment_iff_div.mpr ⟨(μ s).to_real, (μ t).to_real, hs₀, ht₀,
    (average_union hd ht hsμ htμ hfs hft).symm⟩
end

lemma average_union_mem_segment {f : α → E} {s t : set α} (hd : ae_disjoint μ s t)
  (ht : null_measurable_set t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] :=
begin
  by_cases hse : μ s = 0,
  { rw ← ae_eq_empty at hse,
    rw [restrict_congr_set (hse.union eventually_eq.rfl), empty_union],
    exact right_mem_segment _ _ _ },
  { refine mem_segment_iff_div.mpr ⟨(μ s).to_real, (μ t).to_real, ennreal.to_real_nonneg,
      ennreal.to_real_nonneg, _, (average_union hd ht hsμ htμ hfs hft).symm⟩,
    calc 0 < (μ s).to_real : ennreal.to_real_pos hse hsμ
    ... ≤ _ : le_add_of_nonneg_right ennreal.to_real_nonneg }
end

lemma average_mem_open_segment_compl_self [is_finite_measure μ] {f : α → E} {s : set α}
  (hs : null_measurable_set s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) (hfi : integrable f μ) :
  ⨍ x, f x ∂μ ∈ open_segment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) :=
by simpa only [union_compl_self, restrict_univ]
  using average_union_mem_open_segment ae_disjoint_compl_right hs.compl hs₀ hsc₀
    (measure_ne_top _ _) (measure_ne_top _ _) hfi.integrable_on hfi.integrable_on

@[simp] lemma average_const [is_finite_measure μ] [h : μ.ae.ne_bot] (c : E) :
  ⨍ x, c ∂μ = c :=
by simp only [average_eq, integral_const, measure.restrict_apply, measurable_set.univ, one_smul,
  univ_inter, smul_smul, ← ennreal.to_real_inv, ← ennreal.to_real_mul, ennreal.inv_mul_cancel,
  measure_ne_top μ univ, ne.def, measure_univ_eq_zero, ae_ne_bot.1 h, not_false_iff,
  ennreal.one_to_real]

lemma set_average_const {s : set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) :
  ⨍ x in s, c ∂μ = c :=
by simp only [set_average_eq, integral_const, measure.restrict_apply, measurable_set.univ,
  univ_inter, smul_smul, ← ennreal.to_real_inv, ← ennreal.to_real_mul,
  ennreal.inv_mul_cancel hs₀ hs, ennreal.one_to_real, one_smul]

end measure_theory
