/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.interval_integral
import order.filter.at_top_bot

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite/proper integrals,
in the sense that it treats integrals over `[1, +∞)` in the same way as integrals over `[0, 1]`
(for example) : an integral over `[1, +∞)` is **not** defined to be the limit as `x` goes to `+∞` of
the integral over `[1, x]`, which may be named an "improper integral".

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, it is hardly usable to actually compute
integrals on unbounded set, which is way easier using limits. Thus, in this file, we prove
various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `measure_theory.mono_ae_cover`. It's a rather technical
definition whose sole purpose is generalizing and factoring proofs. For a sequence `φ` of subsets
of a measurable space `α` equipped with a measure `μ`, one should think of an hypothesis
`hφ : mono_ae_cover μ φ` as a sufficient condition for being able to interpret
`∫ x, f x ∂μ` (if it exists) as the limit as `n` goes to `∞` of `∫ x in φ n, f x ∂μ`.

When using this definition with a measure restricted to a set `s`, which happens fairly often,
one should not try too hard to use a `mono_ae_cover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`integrable_on_Iic_of_tendsto_interval_integral_norm` where we use `Ioi`s as a `mono_ae_cover`
w.r.t. `μ.restrict (Iic b)`.

## Main statements

- `measure_theory.set_lintegral_tendsto_lintegral` : if `φ` is a `mono_ae_cover` and
  `f` a measurable `ennreal`-valued function, then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ`
  as `n` tends to `+∞`
- `measure_theory.integrable_of_tendsto_integral_norm` : if `φ` is a `mono_ae_cover`,
  `f` measurable and integrable on each `φ n`, and `∫ x in φ n, ∥f x∥ ∂μ` tends to some
  `I : ℝ` as n tends to `+∞`, then `f` is integrable
- `measure_theory.set_integral_tendsto_integral` : if `φ` is a `mono_ae_cover`,
  `f` measurable and integrable (globally), then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ`
  as `n` tends to `+∞`

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis.

-/
open measure_theory filter set
open_locale ennreal nnreal topological_space

namespace measure_theory

section mono_ae_cover

variables {α ι : Type*} [ordered_add_comm_monoid ι]
  [measurable_space α] (μ : measure α)

/-- A sequence `φ` of subsets of `α` is a `mono_ae_cover` w.r.t. a measure `μ`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n`, `φ` is
    monotone, and each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit as `n` goes to `∞` of `∫ x in φ n, f x ∂μ`.

    See for example `measure_theory.lintegral_eq_of_tendsto_lintegral`,
    `measure_theory.integrable_of_tendsto_integral_norm` and
    `measure_theory.integral_eq_of_tendsto_integral`. -/
structure mono_ae_cover (φ : ι → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in at_top, x ∈ φ i)
(mono : monotone φ)
(measurable : ∀ i, measurable_set $ φ i)

variables {μ}

section preorder

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x)
  (ha₂ : tendsto a at_top at_bot) (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma mono_ae_cover_Icc :
  mono_ae_cover μ (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mp $
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  mono := λ i j hij, Icc_subset_Icc (ha₁ hij) (hb₁ hij),
  measurable := λ i, measurable_set_Icc }

lemma mono_ae_cover_Ici :
  mono_ae_cover μ (λ i, Ici $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mono $
    λ i hai, hai ),
  mono := λ i j hij, Ici_subset_Ici.mpr (ha₁ hij),
  measurable := λ i, measurable_set_Ici }

lemma mono_ae_cover_Iic :
  mono_ae_cover μ (λ i, Iic $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ i hbi, hbi ),
  mono := λ i j hij, Iic_subset_Iic.mpr (hb₁ hij),
  measurable := λ i, measurable_set_Iic }

end preorder

section linear_order

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x)
  (ha₂ : tendsto a at_top at_bot)
  (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma mono_ae_cover_Ioo [no_bot_order α] [no_top_order α] :
  mono_ae_cover μ (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mp $
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  mono := λ i j hij, Ioo_subset_Ioo (ha₁ hij) (hb₁ hij),
  measurable := λ i, measurable_set_Ioo }

lemma mono_ae_cover_Ioc [no_bot_order α] : mono_ae_cover μ (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mp $
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  mono := λ i j hij, Ioc_subset_Ioc (ha₁ hij) (hb₁ hij),
  measurable := λ i, measurable_set_Ioc }

lemma mono_ae_cover_Ico [no_top_order α] : mono_ae_cover μ (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mp $
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  mono := λ i j hij, Ico_subset_Ico (ha₁ hij) (hb₁ hij),
  measurable := λ i, measurable_set_Ico }

lemma mono_ae_cover_Ioi [no_bot_order α] :
  mono_ae_cover μ (λ i, Ioi $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mono $
    λ i hai, hai ),
  mono := λ i j hij, Ioi_subset_Ioi (ha₁ hij),
  measurable := λ i, measurable_set_Ioi }

lemma mono_ae_cover_Iio [no_top_order α] :
  mono_ae_cover μ (λ i, Iio $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ i hbi, hbi ),
  mono := λ i j hij, Iio_subset_Iio (hb₁ hij),
  measurable := λ i, measurable_set_Iio }

end linear_order

lemma mono_ae_cover.restrict {φ : ι → set α} (hφ : mono_ae_cover μ φ) {s : set α} :
  mono_ae_cover (μ.restrict s) φ :=
{ ae_eventually_mem := ae_restrict_of_ae hφ.ae_eventually_mem,
  mono := hφ.mono,
  measurable := hφ.measurable }

lemma mono_ae_cover.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  {f : α → β} {φ : ι → set α} (hφ : mono_ae_cover μ φ) :
  ∀ᵐ x ∂μ, tendsto (λ i, (φ i).indicator f x) at_top (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

lemma mono_ae_cover_restrict_of_ae_imp {s : set α} {φ : ι → set α}
  (hs : measurable_set s) (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in at_top, x ∈ φ n)
  (mono : monotone φ) (measurable : ∀ n, measurable_set $ φ n) :
  mono_ae_cover (μ.restrict s) φ :=
{ ae_eventually_mem := by rwa ae_restrict_iff' hs,
  mono := mono,
  measurable := measurable }

lemma mono_ae_cover.inter_restrict {φ : ι → set α} (hφ : mono_ae_cover μ φ)
  {s : set α} (hs : measurable_set s) :
  mono_ae_cover (μ.restrict s) (λ i, φ i ∩ s) :=
mono_ae_cover_restrict_of_ae_imp hs
  (hφ.ae_eventually_mem.mono (λ x hx hxs, hx.mono $ λ i hi, ⟨hi, hxs⟩))
  (λ i j hij, inter_subset_inter_left s (hφ.mono hij))
  (λ i, (hφ.measurable i).inter hs)

end mono_ae_cover

section mono_ae_cover_archimedean

variables {α ι : Type*} [ordered_semiring ι] [archimedean ι]
  [measurable_space α] {μ : measure α}

lemma mono_ae_cover.coe_nat {φ : ι → set α} (hφ : mono_ae_cover μ φ) :
  mono_ae_cover μ (λ (n : ℕ), φ n) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono (λ x, tendsto_coe_nat_at_top_at_top.eventually),
  mono := λ i j hij, hφ.mono (nat.mono_cast hij),
  measurable := λ n, hφ.measurable n }

end mono_ae_cover_archimedean

section lintegral

variables {α ι : Type*} [measurable_space α] {μ : measure α}

lemma set_lintegral_tendsto_of_monotone_set [preorder ι] {φ : ι → set α} (hφ : monotone φ) {f : α → ℝ≥0∞} :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ⨆ (i : ι), ∫⁻ x in φ i, f x ∂μ) :=
tendsto_at_top_csupr
  (λ i j hij, lintegral_mono' (measure.restrict_mono (hφ hij) (le_refl _)) (le_refl _))
  ⟨⊤, λ _ _, le_top⟩

variables [linear_ordered_semiring ι] [archimedean ι]

lemma lintegral_eq_supr {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (i : ι), ∫⁻ x in φ i, f x ∂μ :=
begin
  have hφ' := hφ.coe_nat,
  let F := λ (n : ℕ), indicator (φ n) f,
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    hφ'.ae_tendsto_indicator,
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ'.mono hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have lintegral_F_eq : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ :=
    λ n, lintegral_indicator _ (hφ.measurable n),
  have lintegral_f_mono_iota : monotone (λ i, ∫⁻ x in φ i, f x ∂μ) :=
    (λ i j hij, lintegral_mono' (measure.restrict_mono (hφ.mono hij) (le_refl _)) (le_refl _)),
  rw [lintegral_congr_ae f_eq_supr_F, supr_eq_supr_coe_nat_of_monotone lintegral_f_mono_iota],
  dsimp only,
  conv_rhs {congr, funext, rw ← lintegral_F_eq},
  exact lintegral_supr (λ n, hfm.indicator $ hφ.measurable n) (λ i j hij x, F_mono x hij),
end

lemma set_lintegral_tendsto_lintegral {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
begin
  rw lintegral_eq_supr hφ hfm,
  exact set_lintegral_tendsto_of_monotone_set hφ.2
end

/-- Slight reformulation of `measure_theory.set_lintegral_tendsto_lintegral`. -/
lemma lintegral_eq_of_tendsto_lintegral {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → ℝ≥0∞}
  (I : ℝ≥0∞) (hfm : measurable f) (h : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
tendsto_nhds_unique (set_lintegral_tendsto_lintegral hφ hfm) h

end lintegral

section integrable

variables {α ι : Type*} [linear_ordered_semiring ι] [archimedean ι]
  [measurable_space α] {μ : measure α} {E : Type*} [normed_group E]
  [measurable_space E] [opens_measurable_space E]

lemma integrable_of_tendsto_lintegral_nnnorm {φ : ι → set α}
  (hφ : mono_ae_cover μ φ) {f : α → E} (I : ℝ) (hfm : measurable f)
  (h : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw lintegral_eq_of_tendsto_lintegral hφ _
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) h,
  exact ennreal.of_real_lt_top
end

lemma integrable_of_tendsto_lintegral_nnnorm' {φ : ι → set α}
  (hφ : mono_ae_cover μ φ) {f : α → E} (I : ℝ≥0) (hfm : measurable f)
  (h : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  refine integrable_of_tendsto_lintegral_nnnorm hφ (I : ℝ) hfm _,
  convert h,
  exact ennreal.of_real_coe_nnreal
end

lemma integrable_of_tendsto_integral_norm {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → E}
  (I : ℝ) (hfm : measurable f) (hfi : ∀ i, integrable_on f (φ i) μ)
  (h : tendsto (λ i, ∫ x in φ i, ∥f x∥ ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  conv at h in (integral _ _)
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x)))
    hfm.norm.ae_measurable },
  conv at h in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  have h' : tendsto (λ (i : ι), (∫⁻ (a : α) in φ i, nnnorm (f a) ∂μ)) at_top
    (𝓝 $ ennreal.of_real I),
  { convert ennreal.tendsto_of_real h,
    ext i : 1,
    rw ennreal.of_real_to_real _,
    exact ne_top_of_lt (hfi i).2 },
  exact integrable_of_tendsto_lintegral_nnnorm hφ I hfm h'
end

lemma integrable_of_tendsto_integral_of_nonneg_ae {φ : ι → set α}
  (hφ : mono_ae_cover μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f)
  (hfi : ∀ n, integrable_on f (φ n) μ) (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
integrable_of_tendsto_integral_norm hφ I hfm hfi
  (h.congr $ λ i, integral_congr_ae $ ae_restrict_of_ae $ hf.mono $
    λ x hx, (real.norm_of_nonneg hx).symm)

end integrable

section integral

variables {α ι : Type*} [linear_ordered_semiring ι] [archimedean ι]
  [measurable_space α] {μ : measure α} {E : Type*} [normed_group E]
  [measurable_space E] [borel_space E]

lemma set_integral_norm_tendsto_integral_norm {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → E}
  (hfm : measurable f) (hfi : integrable f μ) :
  tendsto (λ i, ∫ x in φ i, ∥f x∥ ∂μ) at_top (𝓝 $ ∫ x, ∥f x∥ ∂μ) :=
begin
  have mono_integral_norm : monotone (λ i, ∫ x in φ i, ∥f x∥ ∂μ) :=
    (λ (i j : ι) hij, set_integral_mono_set hfi.norm (ae_of_all _ $ λ x, norm_nonneg _)
      (hφ.measurable i) (hφ.measurable j) (ae_of_all _ $ hφ.mono hij)),
  rw tendsto_iff_tendsto_subseq_of_monotone mono_integral_norm tendsto_coe_nat_at_top_at_top,
  suffices : tendsto (λ (n : ℕ), ∫ (x : α), (φ n).indicator (norm ∘ f) x ∂μ) at_top
    (𝓝 (∫ (x : α), ∥f x∥ ∂μ)),
  { convert this,
    ext n,
    rw integral_indicator (hφ.measurable n) },
  refine tendsto_integral_of_dominated_convergence (λ x, ∥f x∥)
    (λ n, (hfm.norm.indicator $ hφ.measurable n).ae_measurable) hfm.norm.ae_measurable hfi.norm
    (λ n, ae_of_all _ $ λ x, _) hφ.coe_nat.ae_tendsto_indicator,
  rw [indicator_comp_of_zero norm_zero, norm_norm],
  exact norm_indicator_le_norm_self _ _
end

variables [normed_space ℝ E] [complete_space E] [topological_space.second_countable_topology E]

lemma set_integral_tendsto_integral {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → E}
  (hfm : measurable f) (hfi : integrable f μ) :
  tendsto (λ i, ∫ x in φ i, f x ∂μ) at_top (𝓝 $ ∫ x, f x ∂μ) :=
begin
  have key₁ : ∀ i, dist (∫ x in φ i, f x ∂μ) (∫ x, f x ∂μ) ≤
    dist (∫ x in φ i, ∥f x∥ ∂μ) (∫ x, ∥f x∥ ∂μ),
  { intro i,
    rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm,
        ← integral_indicator (hφ.measurable i), ← integral_indicator (hφ.measurable i),
        ← integral_sub hfi (hfi.indicator $ hφ.measurable i),
        ← integral_sub hfi.norm (hfi.norm.indicator $ hφ.measurable i)],
    change ∥∫ x, (f - (φ i).indicator f) x ∂μ∥ ≤
      ∥∫ x, ((norm ∘ f) - (φ i).indicator (norm ∘ f)) x ∂μ∥,
    rw [← indicator_compl, ← indicator_compl,
        integral_indicator (hφ.measurable i).compl, integral_indicator (hφ.measurable i).compl],
    convert norm_integral_le_integral_norm f,
    refine real.norm_of_nonneg (integral_nonneg $ λ x, norm_nonneg _) },
  have key₂ := set_integral_norm_tendsto_integral_norm hφ hfm hfi,
  rw metric.tendsto_nhds at ⊢ key₂,
  intros ε hε,
  exact (key₂ ε hε).mono (λ i hi, lt_of_le_of_lt (key₁ i) hi)
end

/-- Slight reformulation of `measure_theory.set_integral_tendsto_integral`. -/
lemma integral_eq_of_tendsto_integral {φ : ι → set α} (hφ : mono_ae_cover μ φ) {f : α → E} (I : E)
  (hfm : measurable f) (hfi : integrable f μ)
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
tendsto_nhds_unique (set_integral_tendsto_integral hφ hfm hfi) h

lemma integral_eq_of_tendsto_integral_of_nonneg_ae {φ : ι → set α}
  (hφ : mono_ae_cover μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f)
  (hfi : ∀ n, integrable_on f (φ n) μ) (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from integrable_of_tendsto_integral_of_nonneg_ae hφ I hf hfm hfi h,
integral_eq_of_tendsto_integral hφ I hfm hfi' h

end integral

section integrable_of_interval_integral

variables {α ι E : Type*} [topological_space α] [linear_order α] [order_closed_topology α]
  [measurable_space α] [opens_measurable_space α] [linear_ordered_semiring ι]
  [archimedean ι] [measurable_space E] [normed_group E] [borel_space E] {μ : measure α}
  {a b : ι → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (hb₁ : monotone b) {f : α → E}
  (hfm : measurable f)

include ha₁ hb₁

include hfm

lemma integrable_of_tendsto_interval_integral_norm [no_bot_order α]
  (I : ℝ) (hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
  (ha₂ : tendsto a at_top at_bot) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a i .. b i, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable f μ :=
begin
  let φ := λ n, Ioc (a n) (b n),
  have hφ : mono_ae_cover μ φ := mono_ae_cover_Ioc ha₁ ha₂ hb₁ hb₂,
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [eventually_ge_at_top (0 : ι), ha₂.eventually (eventually_le_at_bot $ b 0)],
  intros i hi hai,
  have : a i ≤ b i := hai.trans (hb₁ hi),
  exact interval_integral.integral_of_le this
end

omit hb₁

lemma integrable_on_Iic_of_tendsto_interval_integral_norm [no_bot_order α] (I : ℝ) (b : α)
  (hfi : ∀ i, integrable_on f (Ioc (a i) b) μ) (ha₂ : tendsto a at_top at_bot)
  (h : tendsto (λ i, ∫ x in a i .. b, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Iic b) μ :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : mono_ae_cover (μ.restrict $ Iic b) φ := mono_ae_cover_Ioi ha₁ ha₂,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Iic b),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i)],
    exact hfi i },
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

omit ha₁
include hb₁

lemma integrable_on_Ioi_of_tendsto_interval_integral_norm (I : ℝ) (a : α)
  (hfi : ∀ i, integrable_on f (Ioc a (b i)) μ) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a .. b i, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Ioi a) μ :=
begin
  let φ := λ i, Iic (b i),
  have hφ : mono_ae_cover (μ.restrict $ Ioi a) φ := mono_ae_cover_Iic hb₁ hb₂,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Ioi a),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i), inter_comm],
    exact hfi i },
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [hb₂.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integrable_of_interval_integral

section integral_of_interval_integral

variables {α ι E : Type*} [topological_space α] [linear_order α] [order_closed_topology α]
  [measurable_space α] [opens_measurable_space α] [linear_ordered_semiring ι]
  [archimedean ι] [measurable_space E] [normed_group E]
  [topological_space.second_countable_topology E] [complete_space E]
  [normed_space ℝ E] [borel_space E] {μ : measure α} {a b : ι → α}
  (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (hb₁ : monotone b) {f : α → E} (hfm : measurable f)

include hfm ha₁ hb₁

lemma integral_eq_of_tendsto_interval_integral [no_bot_order α] (I : E)
  (hfi : integrable f μ) (ha₂ : tendsto a at_top at_bot) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a i .. b i, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x, f x ∂μ = I :=
begin
  let φ := λ i, Ioc (a i) (b i),
  have hφ : mono_ae_cover μ φ := mono_ae_cover_Ioc ha₁ ha₂ hb₁ hb₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [eventually_ge_at_top (0 : ι), ha₂.eventually (eventually_le_at_bot $ b 0)],
  intros i hi hai,
  have : a i ≤ b i := hai.trans (hb₁ hi),
  exact interval_integral.integral_of_le this
end

omit hb₁

lemma integral_Iic_eq_of_tendsto_interval_integral [no_bot_order α] (I : E) (b : α)
  (hfi : integrable_on f (Iic b) μ) (ha₂ : tendsto a at_top at_bot)
  (h : tendsto (λ i, ∫ x in a i .. b, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x in Iic b, f x ∂μ = I :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : mono_ae_cover (μ.restrict $ Iic b) φ := mono_ae_cover_Ioi ha₁ ha₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

omit ha₁
include hb₁

lemma integral_Ioi_eq_of_tendsto_interval_integral (I : E) (a : α)
  (hfi : integrable_on f (Ioi a) μ) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a .. b i, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x in Ioi a, f x ∂μ = I :=
begin
  let φ := λ i, Iic (b i),
  have hφ : mono_ae_cover (μ.restrict $ Ioi a) φ := mono_ae_cover_Iic hb₁ hb₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [hb₂.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integral_of_interval_integral

end measure_theory
