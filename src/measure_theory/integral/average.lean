/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Yaël Dillies
-/
import measure_theory.integral.set_integral

/-!
# Integral average of a function

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

## TODO

Provide the first moment method for the Lebesgue integral as well. A draft is available on branch
`first_moment_lintegral`.

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

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`) is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

-/

namespace measure_theory
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

@[simp] lemma integral_average [is_finite_measure μ] (f : α → E) :
  ∫ x, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ :=
begin
  unfreezingI { obtain rfl | hμ := eq_or_ne μ 0 },
  { simp only [integral_zero_measure] },
  { rw [integral_const, average_eq,
      smul_inv_smul₀ (to_real_ne_zero.2 ⟨measure_univ_ne_zero.2 hμ, measure_ne_top _ _⟩)] }
end

lemma set_integral_set_average [is_finite_measure μ] (f : α → E) (s : set α) :
  ∫ x in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
integral_average _

lemma integral_sub_average [is_finite_measure μ] (hf : integrable f μ) :
  ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 :=
by rw [integral_sub hf (integrable_const _), integral_average, sub_self]

lemma set_integral_sub_set_average (hs : μ s ≠ ⊤) (hf : integrable_on f s μ) :
  ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
by haveI haveI : fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩; exact integral_sub_average hf

lemma integral_average_sub [is_finite_measure μ] (hf : integrable f μ) :
  ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 :=
by rw [integral_sub (integrable_const _) hf, integral_average, sub_self]

lemma set_integral_set_average_sub (hs : μ s ≠ ⊤) (hf : integrable_on f s μ) :
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

lemma average_to_real {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (hf' : ∀ᵐ x ∂μ, f x < ⊤) :
  ⨍ x, (f x).to_real ∂μ = (∫⁻ x, f x ∂μ / μ univ).to_real :=
begin
  obtain rfl | hμ := eq_or_ne μ 0,
  { simp },
  { rw [average_eq, smul_eq_mul, to_real_div, ←integral_to_real hf hf', div_eq_inv_mul] }
end

lemma set_average_to_real {f : α → ℝ≥0∞} (hf : ae_measurable f (μ.restrict s))
  (hf' : ∀ᵐ x ∂(μ.restrict s), f x < ⊤) :
  ⨍ x in s, (f x).to_real ∂μ = (∫⁻ x in s, f x ∂μ / μ s).to_real :=
by simpa using average_to_real hf hf'

/-! ### First moment method -/

section first_moment
variables {N : set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_average_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | f x ≤ ⨍ a in s, f a ∂μ} :=
begin
  obtain ⟨t, hts, ht, hμts⟩ := hs.exists_measurable_subset_ae_eq,
  replace hf := hf.mono_set hts,
  simp_rw [←set_of_inter_eq_sep, ←set_average_congr_set_ae hμts,
    ←measure_congr ((eventually_eq.refl _ _).inter hμts)],
  rw ←measure_congr hμts at hμ hμ₁,
  refine pos_iff_ne_zero.2 (λ H, (set_integral_sub_set_average hμ₁ hf).not_gt $
    (set_integral_pos_iff_support_of_nonneg_ae _ $ hf.sub $ integrable_on_const.2 $
    or.inr $ lt_top_iff_ne_top.2 hμ₁).2 _),
  { change _ = _,
    simp only [compl_set_of, ht, pi.zero_apply, pi.sub_apply, sub_nonneg, not_le,
      measure.restrict_apply'],
    exact eq_bot_mono (measure_mono $ inter_subset_inter_left _ $
      set_of_subset_set_of.2 $ λ _, le_of_lt) H },
  { rwa [pos_iff_ne_zero, inter_comm, ←diff_compl, ←diff_inter_self_eq_diff, measure_diff_null],
    exact eq_bot_mono (measure_mono $ inter_subset_inter_left _ $ λ a ha,
      (sub_eq_zero.1 $ of_not_not ha).le) H }
end

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_set_average_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | ⨍ a in s, f a ∂μ ≤ f x} :=
by simpa [integral_neg, neg_div] using measure_le_set_average_pos hμ hμ₁ hf.neg hs

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_set_average (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_average_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_set_average_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_average_le_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

variables [is_finite_measure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_average_pos (hμ : μ ≠ 0) (hf : integrable f μ) : 0 < μ {x | f x ≤ ⨍ a, f a ∂μ} :=
by simpa using measure_le_set_average_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on null_measurable_set_univ

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_average_le_pos (hμ : μ ≠ 0) (hf : integrable f μ) : 0 < μ {x | ⨍ a, f a ∂μ ≤ f x} :=
by simpa using measure_set_average_le_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on null_measurable_set_univ

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_average (hμ : μ ≠ 0) (hf : integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_integral_le (hμ : μ ≠ 0) (hf : integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
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

end first_moment

end measure_theory
