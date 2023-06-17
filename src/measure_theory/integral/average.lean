/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Yaël Dillies
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

Both have a version for the Lebesgue integral rather than Bochner.

We prove several version of the first moment method: An integrable function is below/above its
average on a set of positive measure.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `measure_theory.integrable.to_average`.

## Tags

integral, center mass, average value
-/

open ennreal measure_theory measure_theory.measure metric set filter topological_space function
open_locale topology big_operators ennreal convex

variables {α E F : Type*} {m0 : measurable_space α}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {μ : measure α} {s t : set α}

/-!
### Average value of a function w.r.t. a measure

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`, `⨍⁻ x, f x ∂μ`)
is defined as `(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.
-/

namespace measure_theory
section ennreal
variables (μ) {f g : α → ℝ≥0∞}
include m0

/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍⁻ x, f x ∂μ`. It is defined as
`μ univ⁻¹ * ∫⁻ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an infinite
measure. If `μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ` (defined as `⨍⁻ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂((μ univ)⁻¹ • μ)

notation `⨍⁻` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := laverage μ r
notation `⨍⁻` binders `, ` r:(scoped:60 f, laverage volume f) := r
notation `⨍⁻` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
  laverage (measure.restrict μ s) r
notation `⨍⁻` binders ` in ` s `, ` r:(scoped:60 f, laverage (measure.restrict volume s) f) := r

@[simp] lemma laverage_zero : ⨍⁻ x, (0 : ℝ≥0∞) ∂μ = 0 := by rw [laverage, lintegral_zero]

@[simp] lemma laverage_zero_measure (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂(0 : measure α) = 0 :=
by simp [laverage]

lemma laverage_eq' (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂((μ univ)⁻¹ • μ) := rfl

lemma laverage_eq (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ / μ univ :=
by rw [laverage_eq', lintegral_smul_measure, ennreal.div_eq_inv_mul]

lemma laverage_eq_lintegral [is_probability_measure μ] (f : α → ℝ≥0∞) :
  ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw [laverage, measure_univ, inv_one, one_smul]

@[simp] lemma measure_mul_laverage [is_finite_measure μ] (f : α → ℝ≥0∞) :
  μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ :=
begin
  cases eq_or_ne μ 0 with hμ hμ,
  { rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero] },
  { rw [laverage_eq, ennreal.mul_div_cancel' (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)] }
end

lemma set_laverage_eq (f : α → ℝ≥0∞) (s : set α) : ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ / μ s :=
by rw [laverage_eq, restrict_apply_univ]

lemma set_laverage_eq' (f : α → ℝ≥0∞) (s : set α) :
  ⨍⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂((μ s)⁻¹ • μ.restrict s) :=
by simp only [laverage_eq', restrict_apply_univ]

variable {μ}

lemma laverage_congr {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ :=
by simp only [laverage_eq, lintegral_congr_ae h]

lemma set_laverage_congr_set_ae (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ :=
by simp only [set_laverage_eq, set_lintegral_congr h, measure_congr h]

lemma laverage_ne_top [μ.ae.ne_bot] (hf : ∫⁻ x, f x ∂μ ≠ ∞) : ⨍⁻ x, f x ∂μ ≠ ∞ :=
by { rw laverage_eq, exact div_eq_top.not.2 (λ H, H.elim (λ H, ae_ne_bot.1 ‹_› $
  measure_univ_eq_zero.1 H.2) $ λ H, hf H.1) }

lemma set_laverage_ne_top (hs : μ s ≠ 0) (hf : ∫⁻ x in s, f x ∂μ ≠ ∞) : ⨍⁻ x in s, f x ∂μ ≠ ∞ :=
by { rw set_laverage_eq, refine div_eq_top.not.2 (λ H, H.elim (λ H, hs H.2) $ λ H, hf H.1) }

lemma laverage_add_measure [is_finite_measure μ] {ν : measure α} [is_finite_measure ν] :
  ⨍⁻ x, f x ∂(μ + ν) =
    μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν :=
by simp only [←ennreal.mul_div_right_comm, measure_mul_laverage, ←ennreal.add_div,
  ←lintegral_add_measure, ←measure.add_apply, ←laverage_eq]

lemma measure_mul_set_laverage (f : α → ℝ≥0∞) (h : μ s ≠ ∞) :
  μ s * ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ :=
by { haveI := fact.mk h.lt_top, rw [← measure_mul_laverage, restrict_apply_univ] }

lemma laverage_union (hd : ae_disjoint μ s t) (ht : null_measurable_set t μ) (hsμ : μ s ≠ ∞)
  (htμ : μ t ≠ ∞) :
  ⨍⁻ x in s ∪ t, f x ∂μ =
    μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t) * ⨍⁻ x in t, f x ∂μ :=
begin
  haveI := fact.mk hsμ.lt_top, haveI := fact.mk htμ.lt_top,
  rw [restrict_union₀ hd ht, laverage_add_measure, restrict_apply_univ, restrict_apply_univ]
end

lemma laverage_union_mem_open_segment (hd : ae_disjoint μ s t) (ht : null_measurable_set t μ)
  (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
  ⨍⁻ x in s ∪ t, f x ∂μ ∈ open_segment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t, f x ∂μ) :=
begin
  refine ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ennreal.div_pos hs₀ $ add_ne_top.2 ⟨hsμ, htμ⟩,
    ennreal.div_pos ht₀ $ add_ne_top.2 ⟨hsμ, htμ⟩, _, (laverage_union hd ht hsμ htμ).symm⟩,
  rw [←ennreal.add_div, ennreal.div_self (add_eq_zero.not.2 $ λ h, hs₀ h.1)
    (add_ne_top.2 ⟨hsμ, htμ⟩)],
end

lemma laverage_union_mem_segment (hd : ae_disjoint μ s t) (ht : null_measurable_set t μ)
  (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
  ⨍⁻ x in s ∪ t, f x ∂μ ∈ [⨍⁻ x in s, f x ∂μ -[ℝ≥0∞] ⨍⁻ x in t, f x ∂μ] :=
begin
  by_cases hs₀ : μ s = 0,
  { rw ← ae_eq_empty at hs₀,
    rw [restrict_congr_set (hs₀.union eventually_eq.rfl), empty_union],
    exact right_mem_segment _ _ _ },
  { refine ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le _, zero_le _, _,
    (laverage_union hd ht hsμ htμ).symm⟩,
    rw [←ennreal.add_div, ennreal.div_self (add_eq_zero.not.2 $ λ h, hs₀ h.1)
      (add_ne_top.2 ⟨hsμ, htμ⟩)] }
end

lemma laverage_mem_open_segment_compl_self [is_finite_measure μ] (hs : null_measurable_set s μ)
  (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) :
  ⨍⁻ x, f x ∂μ ∈ open_segment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ) :=
by simpa only [union_compl_self, restrict_univ]
  using laverage_union_mem_open_segment ae_disjoint_compl_right hs.compl hs₀ hsc₀
    (measure_ne_top _ _) (measure_ne_top _ _)

@[simp] lemma laverage_const [is_finite_measure μ] [h : μ.ae.ne_bot] (c : ℝ≥0∞) : ⨍⁻ x, c ∂μ = c :=
by simp only [laverage_eq, lintegral_const, measure.restrict_apply, measurable_set.univ, univ_inter,
  div_eq_mul_inv, mul_assoc, ennreal.mul_inv_cancel, mul_one, measure_ne_top μ univ, ne.def,
  measure_univ_ne_zero, ae_ne_bot.1 h, not_false_iff]

lemma set_laverage_const {s : set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : ℝ≥0∞) :
  ⨍⁻ x in s, c ∂μ = c :=
by simp only [set_laverage_eq, lintegral_const, measure.restrict_apply, measurable_set.univ,
  univ_inter, div_eq_mul_inv, mul_assoc, ennreal.mul_inv_cancel hs₀ hs, mul_one]

@[simp] lemma lintegral_laverage (μ : measure α) [is_finite_measure μ] (f : α → ℝ≥0∞) :
  ∫⁻ x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ :=
begin
  unfreezingI { obtain rfl | hμ := eq_or_ne μ 0 },
  { simp },
  { rw [lintegral_const, laverage_eq,
      ennreal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)] }
end

lemma set_lintegral_set_laverage (μ : measure α) [is_finite_measure μ] (f : α → ℝ≥0∞) (s : set α) :
  ∫⁻ x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ :=
lintegral_laverage _ _

end ennreal

section normed_add_comm_group
variables (μ) {f g : α → E}
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

lemma set_average_congr_set_ae (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ :=
by simp only [set_average_eq, set_integral_congr_set_ae h, measure_congr h]

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

@[simp] lemma integral_average (μ : measure α) [is_finite_measure μ] (f : α → E) :
  ∫ x, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ :=
begin
  unfreezingI { obtain rfl | hμ := eq_or_ne μ 0 },
  { simp only [integral_zero_measure] },
  { rw [integral_const, average_eq,
      smul_inv_smul₀ (to_real_ne_zero.2 ⟨measure_univ_ne_zero.2 hμ, measure_ne_top _ _⟩)] }
end

lemma set_integral_set_average (μ : measure α) [is_finite_measure μ] (f : α → E) (s : set α) :
  ∫ x in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
integral_average _ _

lemma integral_sub_average (μ : measure α) [is_finite_measure μ] (f : α → E) :
  ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_sub hf (integrable_const _), integral_average, sub_self] },
  refine integral_undef (λ h, hf _),
  convert h.add (integrable_const _),
  exact (sub_add_cancel _ _).symm,
end

lemma set_integral_sub_set_average (hs : μ s ≠ ∞) (f : α → E) :
  ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
by haveI haveI : fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩; exact integral_sub_average _ _

lemma integral_average_sub [is_finite_measure μ] (hf : integrable f μ) :
  ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 :=
by rw [integral_sub (integrable_const _) hf, integral_average, sub_self]

lemma set_integral_set_average_sub (hs : μ s ≠ ∞) (hf : integrable_on f s μ) :
  ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
by haveI haveI : fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩; exact integral_average_sub hf

end normed_add_comm_group

lemma of_real_average {f : α → ℝ} (hf : integrable f μ) (hf₀ : 0 ≤ᵐ[μ] f) :
  ennreal.of_real (⨍ x, f x ∂μ) = (∫⁻ x, ennreal.of_real (f x) ∂μ) / μ univ :=
begin
  obtain rfl | hμ := eq_or_ne μ 0,
  { simp },
  { rw [average_eq, smul_eq_mul, ←to_real_inv, of_real_mul (to_real_nonneg),
      of_real_to_real (inv_ne_top.2 $ measure_univ_ne_zero.2 hμ),
      of_real_integral_eq_lintegral_of_real hf hf₀, ennreal.div_eq_inv_mul] }
end

lemma of_real_set_average {f : α → ℝ} (hf : integrable_on f s μ)
  (hf₀ : 0 ≤ᵐ[μ.restrict s] f) :
  ennreal.of_real (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ennreal.of_real (f x) ∂μ) / μ s :=
by simpa using of_real_average hf hf₀

lemma to_real_laverage {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (hf' : ∀ᵐ x ∂μ, f x ≠ ∞) :
  (⨍⁻ x, f x ∂μ).to_real = ⨍ x, (f x).to_real ∂μ :=
begin
  obtain rfl | hμ := eq_or_ne μ 0,
  { simp },
  { rw [average_eq, laverage_eq, smul_eq_mul, to_real_div, div_eq_inv_mul,
      ←integral_to_real hf (hf'.mono $ λ _, lt_top_iff_ne_top.2)] }
end

lemma to_real_set_laverage {f : α → ℝ≥0∞} (hf : ae_measurable f (μ.restrict s))
  (hf' : ∀ᵐ x ∂(μ.restrict s), f x ≠ ∞) :
  (∫⁻ x in s, f x ∂μ / μ s).to_real = ⨍ x in s, (f x).to_real ∂μ :=
by simpa [laverage_eq] using to_real_laverage hf hf'

/-! ### First moment method -/

section first_moment_real
variables {N : set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_average_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ) :
  0 < μ {x ∈ s | f x ≤ ⨍ a in s, f a ∂μ} :=
begin
  refine pos_iff_ne_zero.2 (λ H, _),
  replace H : (μ.restrict s) {x | f x ≤ ⨍ a in s, f a ∂μ} = 0,
  { rwa [restrict_apply₀, inter_comm],
    exact ae_strongly_measurable.null_measurable_set_le hf.1 ae_strongly_measurable_const },
  haveI : is_finite_measure (μ.restrict s) :=
    ⟨by simpa only [measure.restrict_apply, measurable_set.univ, univ_inter] using hμ₁.lt_top⟩,
  refine (integral_sub_average (μ.restrict s) f).not_gt _,
  refine (set_integral_pos_iff_support_of_nonneg_ae _ _).2 _,
  { refine eq_bot_mono (measure_mono (λ x hx, _)) H,
    simp only [pi.zero_apply, sub_nonneg, mem_compl_iff, mem_set_of_eq, not_le] at hx,
    exact hx.le },
  { exact hf.sub (integrable_on_const.2 $ or.inr $ lt_top_iff_ne_top.2 hμ₁) },
  { rwa [pos_iff_ne_zero, inter_comm, ←diff_compl, ←diff_inter_self_eq_diff, measure_diff_null],
    refine eq_bot_mono (measure_mono _) (measure_inter_eq_zero_of_restrict H),
    exact inter_subset_inter_left _ (λ a ha, (sub_eq_zero.1 $ of_not_not ha).le) }
end

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_set_average_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ) :
  0 < μ {x ∈ s | ⨍ a in s, f a ∂μ ≤ f x} :=
by simpa [integral_neg, neg_div] using measure_le_set_average_pos hμ hμ₁ hf.neg

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_set_average (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ) :
  ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_average_pos hμ hμ₁ hf).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_set_average_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ) :
  ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_average_le_pos hμ hμ₁ hf).ne'
  in ⟨x, hx, h⟩

section finite_measure
variables [is_finite_measure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_average_pos (hμ : μ ≠ 0) (hf : integrable f μ) : 0 < μ {x | f x ≤ ⨍ a, f a ∂μ} :=
by simpa using measure_le_set_average_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_average_le_pos (hμ : μ ≠ 0) (hf : integrable f μ) : 0 < μ {x | ⨍ a, f a ∂μ ≤ f x} :=
by simpa using measure_set_average_le_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_average (hμ : μ ≠ 0) (hf : integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_average_le (hμ : μ ≠ 0) (hf : integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
lemma exists_not_mem_null_le_average (hμ : μ ≠ 0) (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ⨍ a, f a ∂μ :=
begin
  have := measure_le_average_pos hμ hf,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
lemma exists_not_mem_null_average_le (hμ : μ ≠ 0) (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, ⨍ a, f a ∂μ ≤ f x :=
by simpa [integral_neg, neg_div] using exists_not_mem_null_le_average hμ hf.neg hN

end finite_measure

section probability_measure
variables [is_probability_measure μ]

/-- **First moment method**. An integrable function is smaller than its integral on a set of
positive measure. -/
lemma measure_le_integral_pos (hf : integrable f μ) : 0 < μ {x | f x ≤ ∫ a, f a ∂μ} :=
by simpa only [average_eq_integral]
  using measure_le_average_pos (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. An integrable function is greater than its integral on a set of
positive measure. -/
lemma measure_integral_le_pos (hf : integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ ≤ f x} :=
by simpa only [average_eq_integral]
  using measure_average_le_pos (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral. -/
lemma exists_le_integral (hf : integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ :=
by simpa only [average_eq_integral] using exists_le_average (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. The maximum of an integrable function is greater than its integral. -/
lemma exists_integral_le (hf : integrable f μ) : ∃ x, ∫ a, f a ∂μ ≤ f x :=
by simpa only [average_eq_integral] using exists_average_le (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral,
while avoiding a null set. -/
lemma exists_not_mem_null_le_integral (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ∫ a, f a ∂μ :=
by simpa only [average_eq_integral]
  using exists_not_mem_null_le_average (is_probability_measure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of an integrable function is greater than its integral,
while avoiding a null set. -/
lemma exists_not_mem_null_integral_le (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, ∫ a, f a ∂μ ≤ f x :=
by simpa only [average_eq_integral]
  using exists_not_mem_null_average_le (is_probability_measure.ne_zero μ) hf hN

end probability_measure
end first_moment_real

section first_moment_ennreal
variables {N : set α} {f : α → ℝ≥0∞}

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_laverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞)
  (hf : ae_measurable f (μ.restrict s)) (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | f x ≤ ⨍⁻ a in s, f a ∂μ} :=
begin
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞,
  { simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ },
  have := measure_le_set_average_pos hμ hμ₁ (integrable_to_real_of_lintegral_ne_top hf h),
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs],
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs,
    ←measure_diff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this,
  refine this.trans_le (measure_mono _),
  rintro x ⟨hfx, hx⟩,
  dsimp at hfx,
  rwa [←to_real_laverage hf, to_real_le_to_real hx (set_laverage_ne_top hμ h)] at hfx,
  simp_rw [ae_iff, not_ne_iff],
  exact measure_eq_top_of_lintegral_ne_top hf h,
end

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
lemma measure_set_laverage_le_pos (hμ : μ s ≠ 0) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) :
  0 < μ {x ∈ s | ⨍⁻ a in s, f a ∂μ ≤ f x} :=
begin
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞,
  { simp [set_laverage_eq, hμ₁] },
  have := measure_set_average_le_pos hμ hμ₁ (integrable_to_real_of_lintegral_ne_top hf hint),
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs],
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs,
    ←measure_diff_null (measure_eq_top_of_lintegral_ne_top hf hint)] at this,
  refine this.trans_le (measure_mono _),
  rintro x ⟨hfx, hx⟩,
  dsimp at hfx,
  rwa [←to_real_laverage hf, to_real_le_to_real (set_laverage_ne_top hμ hint) hx] at hfx,
  simp_rw [ae_iff, not_ne_iff],
  exact measure_eq_top_of_lintegral_ne_top hf hint,
end

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
lemma exists_le_set_laverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, f x ≤ ⨍⁻ a in s, f a ∂μ :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_laverage_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
lemma exists_set_laverage_le (hμ : μ s ≠ 0) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hint : ∫⁻ a in s, f a ∂μ ≠ ⊤) :
  ∃ x ∈ s, ⨍⁻ a in s, f a ∂μ ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_laverage_le_pos hμ hf hs hint).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
lemma measure_laverage_le_pos (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
  0 < μ {x | ⨍⁻ a, f a ∂μ ≤ f x} :=
by simpa [hint] using measure_set_laverage_le_pos (measure_univ_ne_zero.2 hμ) hf.restrict
  null_measurable_set_univ

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
lemma exists_laverage_le (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
  ∃ x, ⨍⁻ a, f a ∂μ ≤ f x :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hf hint).ne' in ⟨x, hx⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean, while
avoiding a null set. -/
lemma exists_not_mem_null_laverage_le (hμ : μ ≠ 0) (hf : ae_measurable f μ)
  (hint : ∫⁻ (a : α), f a ∂μ ≠ ⊤) (hN : μ N = 0) :
  ∃ x ∉ N, ⨍⁻ a, f a ∂μ ≤ f x :=
begin
  have := measure_laverage_le_pos hμ hf hint,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

section finite_measure
variables [is_finite_measure μ]

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_laverage_pos (hμ : μ ≠ 0) (hf : ae_measurable f μ) :
  0 < μ {x | f x ≤ ⨍⁻ a, f a ∂μ} :=
by simpa using measure_le_set_laverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.restrict null_measurable_set_univ

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
lemma exists_le_laverage (hμ : μ ≠ 0) (hf : ae_measurable f μ) : ∃ x, f x ≤ ⨍⁻ a, f a ∂μ :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The minimum of a measurable function is smaller than its mean, while
avoiding a null set. -/
lemma exists_not_mem_null_le_laverage (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ⨍⁻ a, f a ∂μ :=
begin
  have := measure_le_laverage_pos hμ hf,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

end finite_measure

section probability_measure
variables [is_probability_measure μ]

/-- **First moment method**. A measurable function is smaller than its integral on a set of
positive measure. -/
lemma measure_le_lintegral_pos (hf : ae_measurable f μ) : 0 < μ {x | f x ≤ ∫⁻ a, f a ∂μ} :=
by simpa only [laverage_eq_lintegral]
  using measure_le_laverage_pos (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. A measurable function is greater than its integral on a set of
positive measure. -/
lemma measure_lintegral_le_pos (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
  0 < μ {x | ∫⁻ a, f a ∂μ ≤ f x} :=
by simpa only [laverage_eq_lintegral]
  using measure_laverage_le_pos (is_probability_measure.ne_zero μ) hf hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral. -/
lemma exists_le_lintegral (hf : ae_measurable f μ) : ∃ x, f x ≤ ∫⁻ a, f a ∂μ :=
by simpa only [laverage_eq_lintegral]
  using exists_le_laverage (is_probability_measure.ne_zero μ) hf

/-- **First moment method**. The maximum of a measurable function is greater than its integral. -/
lemma exists_lintegral_le (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
  ∃ x, ∫⁻ a, f a ∂μ ≤ f x :=
by simpa only [laverage_eq_lintegral]
  using exists_laverage_le (is_probability_measure.ne_zero μ) hf hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral,
while avoiding a null set. -/
lemma exists_not_mem_null_le_lintegral (hf : ae_measurable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ∫⁻ a, f a ∂μ :=
by simpa only [laverage_eq_lintegral]
  using exists_not_mem_null_le_laverage (is_probability_measure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of a measurable function is greater than its integral,
while avoiding a null set. -/
lemma exists_not_mem_null_lintegral_le (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ∞)
  (hN : μ N = 0) : ∃ x ∉ N, ∫⁻ a, f a ∂μ ≤ f x :=
by simpa only [laverage_eq_lintegral]
  using exists_not_mem_null_laverage_le (is_probability_measure.ne_zero μ) hf hint hN

end probability_measure
end first_moment_ennreal
end measure_theory
