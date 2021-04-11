/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.interval_integral

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

## Main statements

-/
open measure_theory filter set
open_locale ennreal nnreal topological_space

namespace measure_theory

section growing_family

variables {α : Type*} [measurable_space α] (μ : measure α)

/-- A sequence `φ` of subsets of `α` is a `growing_family` w.r.t. a measure `μ`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n`, `φ` is
    monotone, and each `φ n` is measurable.

    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit as `n` goes to `∞` of `∫ x in φ n, f x ∂μ`.

    See for example `measure_theory.lintegral_eq_of_tendsto_lintegral`,
    `measure_theory.integrable_of_tendsto_integral_norm` and
    `measure_theory.integral_eq_of_tendsto_integral`. -/
structure growing_family (φ : ℕ → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ n in at_top, x ∈ φ n)
(mono : monotone φ)
(measurable : ∀ n, measurable_set $ φ n)

variables {μ}

section preorder

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ℕ → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x)
  (ha₂ : tendsto a at_top at_bot) (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma growing_family_Icc :
  growing_family μ (λ n, Icc (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mp $
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Icc_subset_Icc (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Icc }

lemma growing_family_Ici :
  growing_family μ (λ n, Ici $ a n) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mono $
    λ n han, han ),
  mono := λ i j hij, Ici_subset_Ici.mpr (ha₁ hij),
  measurable := λ n, measurable_set_Ici }

lemma growing_family_Iic :
  growing_family μ (λ n, Iic $ b n) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ n han, han ),
  mono := λ i j hij, Iic_subset_Iic.mpr (hb₁ hij),
  measurable := λ n, measurable_set_Iic }

end preorder

section linear_order

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ℕ → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x)
  (ha₂ : tendsto a at_top at_bot)
  (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma growing_family_Ioo [no_bot_order α] [no_top_order α] :
  growing_family μ (λ n, Ioo (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mp $
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ioo_subset_Ioo (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ioo }

lemma growing_family_Ioc [no_bot_order α] : growing_family μ (λ n, Ioc (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mp $
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ioc_subset_Ioc (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ioc }

lemma growing_family_Ico [no_top_order α] : growing_family μ (λ n, Ico (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_le_at_bot x).mp $
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ico_subset_Ico (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ico }

lemma growing_family_Ioi [no_bot_order α] :
  growing_family μ (λ n, Ioi $ a n) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha₂.eventually $ eventually_lt_at_bot x).mono $
    λ n han, han ),
  mono := λ i j hij, Ioi_subset_Ioi (ha₁ hij),
  measurable := λ n, measurable_set_Ioi }

lemma growing_family_Iio [no_top_order α] :
  growing_family μ (λ n, Iio $ b n) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ n han, han ),
  mono := λ i j hij, Iio_subset_Iio (hb₁ hij),
  measurable := λ n, measurable_set_Iio }

end linear_order

lemma growing_family.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  {f : α → β} {φ : ℕ → set α} (hφ : growing_family μ φ) :
  ∀ᵐ x ∂μ, tendsto (λ n, (φ n).indicator f x) at_top (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

lemma growing_family_restrict_of_ae_imp {s : set α} {φ : ℕ → set α}
  (hs : measurable_set s) (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in at_top, x ∈ φ n)
  (mono : monotone φ) (measurable : ∀ n, measurable_set $ φ n) :
  growing_family (μ.restrict s) φ :=
{ ae_eventually_mem := by rwa ae_restrict_iff' hs,
  mono := mono,
  measurable := measurable }

lemma growing_family.inter_restrict {φ : ℕ → set α} (hφ : growing_family μ φ)
  {s : set α} (hs : measurable_set s) :
  growing_family (μ.restrict s) (λ n, φ n ∩ s) :=
growing_family_restrict_of_ae_imp hs
  (hφ.ae_eventually_mem.mono (λ x hx hxs, hx.mono $ λ n hn, ⟨hn, hxs⟩))
  (λ i j hij, inter_subset_inter_left s (hφ.mono hij))
  (λ n, (hφ.measurable n).inter hs)

end growing_family

section lintegral

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma lintegral_eq_supr {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let F := λ n, indicator (φ n) f,
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    hφ.ae_tendsto_indicator,
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ.mono hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have lintegral_F_eq : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ :=
    λ n, lintegral_indicator _ (hφ.measurable n),
  rw lintegral_congr_ae f_eq_supr_F,
  conv_rhs {congr, funext, rw ← lintegral_F_eq},
  exact lintegral_supr (λ n, hfm.indicator $ hφ.measurable n) (λ i j hij x, F_mono x hij)
end

lemma tendsto_set_lintegral_of_monotone_set {φ : ℕ → set α} (hφ : monotone φ) {f : α → ℝ≥0∞} :
  tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 $ ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ) :=
tendsto_at_top_csupr
  (λ i j hij, lintegral_mono' (measure.restrict_mono (hφ hij) (le_refl _)) (le_refl _))
  ⟨⊤, λ _ _, le_top⟩

lemma lintegral_eq_of_tendsto_lintegral {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ≥0∞}
  (I : ℝ≥0∞) (hfm : measurable f) (h : tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
begin
  convert lintegral_eq_supr hφ hfm,
  refine tendsto_nhds_unique h (tendsto_set_lintegral_of_monotone_set hφ.mono)
end

end lintegral

section integrable

variables {α : Type*} [measurable_space α] {μ : measure α} {E : Type*} [normed_group E]
  [measurable_space E] [opens_measurable_space E]

lemma integrable_of_tendsto_lintegral_nnnorm {φ : ℕ → set α}
  (hφ : growing_family μ φ) {f : α → E} (I : ℝ) (hfm : measurable f)
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw lintegral_eq_of_tendsto_lintegral hφ _
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) h,
  exact ennreal.of_real_lt_top
end

lemma integrable_of_tendsto_lintegral_nnnorm' {φ : ℕ → set α}
  (hφ : growing_family μ φ) {f : α → E} (I : ℝ≥0) (hfm : measurable f)
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  refine integrable_of_tendsto_lintegral_nnnorm hφ (I : ℝ) hfm _,
  convert h,
  exact ennreal.of_real_coe_nnreal
end

lemma integrable_of_tendsto_integral_norm {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → E}
  (I : ℝ) (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ)
  (h : tendsto (λ n, ∫ x in φ n, ∥f x∥ ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  conv at h in (integral _ _)
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x)))
    hfm.norm.ae_measurable },
  conv at h in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  have h' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ)) at_top
    (𝓝 $ ennreal.of_real I),
  { convert ennreal.tendsto_of_real h,
    ext n : 1,
    rw ennreal.of_real_to_real _,
    exact ne_top_of_lt (hfi n).2 },
  exact integrable_of_tendsto_lintegral_nnnorm hφ I hfm h'
end

lemma integrable_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α}
  (hφ : growing_family μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f)
  (hfi : ∀ n, integrable_on f (φ n) μ) (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
integrable_of_tendsto_integral_norm hφ I hfm hfi
  (h.congr $ λ n, integral_congr_ae $ ae_restrict_of_ae $ hf.mono $
    λ x hx, (real.norm_of_nonneg hx).symm)

end integrable

section integral

variables {α : Type*} [measurable_space α] {μ : measure α} {E : Type*} [normed_group E]
  [measurable_space E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [topological_space.second_countable_topology E]

lemma integral_eq_of_tendsto_integral {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → E} (I : E)
  (hfm : measurable f) (hfi : integrable f μ)
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
begin
  refine tendsto_nhds_unique _ h,
  suffices : tendsto (λ (n : ℕ), ∫ (x : α), (φ n).indicator f x ∂μ) at_top (𝓝 (∫ (x : α), f x ∂μ)),
  { convert this,
    ext n,
    rw integral_indicator (hφ.measurable n) },
  exact tendsto_integral_of_dominated_convergence (λ x, ∥f x∥)
    (λ n, (hfm.indicator $ hφ.measurable n).ae_measurable) hfm.ae_measurable hfi.norm
    (λ n, ae_of_all _ $ norm_indicator_le_norm_self f) hφ.ae_tendsto_indicator
end

lemma integral_eq_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α}
  (hφ : growing_family μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f)
  (hfi : ∀ n, integrable_on f (φ n) μ) (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from integrable_of_tendsto_integral_of_nonneg_ae hφ I hf hfm hfi h,
integral_eq_of_tendsto_integral hφ I hfm hfi' h

end integral

section integrable_of_interval_integral

variables {α : Type*} {E : Type*} [topological_space α] [linear_order α] [order_closed_topology α]
  [measurable_space α] [opens_measurable_space α] [measurable_space E]
  [normed_group E] [borel_space E] {μ : measure α} {a b : ℕ → α}
  (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (hb₁ : monotone b) {f : α → E} (hfm : measurable f)

include ha₁ hb₁

include hfm

lemma integrable_of_tendsto_interval_integral_norm [no_bot_order α]
  (I : ℝ) (hfi : ∀ n, integrable_on f (Ioc (a n) (b n)) μ)
  (ha₂ : tendsto a at_top at_bot) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ n, ∫ x in a n .. b n, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable f μ :=
begin
  let φ := λ n, Ioc (a n) (b n),
  have hφ : growing_family μ φ := growing_family_Ioc ha₁ ha₂ hb₁ hb₂,
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b 0)],
  intros n han,
  have : a n ≤ b n := han.trans (hb₁ $ zero_le n),
  exact interval_integral.integral_of_le this
end

omit hb₁

lemma integrable_on_Iic_of_tendsto_interval_integral_norm [no_bot_order α] (I : ℝ) (b : α)
  (hfi : ∀ n, integrable_on f (Ioc (a n) b) μ) (ha₂ : tendsto a at_top at_bot)
  (h : tendsto (λ n, ∫ x in a n .. b, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Iic b) μ :=
begin
  let φ := λ n, Ioi (a n),
  have hφ : growing_family (μ.restrict $ Iic b) φ := growing_family_Ioi ha₁ ha₂,
  have hfi : ∀ n, integrable_on f (φ n) (μ.restrict $ Iic b),
  { intro n,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable n)],
    exact hfi n },
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b)],
  intros n han,
  rw [interval_integral.integral_of_le han, measure.restrict_restrict (hφ.measurable n)],
  refl
end

omit ha₁
include hb₁

lemma integrable_on_Ioi_of_tendsto_interval_integral_norm (I : ℝ) (a : α)
  (hfi : ∀ n, integrable_on f (Ioc a (b n)) μ) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ n, ∫ x in a .. b n, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Ioi a) μ :=
begin
  let φ := λ n, Iic (b n),
  have hφ : growing_family (μ.restrict $ Ioi a) φ := growing_family_Iic hb₁ hb₂,
  have hfi : ∀ n, integrable_on f (φ n) (μ.restrict $ Ioi a),
  { intro n,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable n), inter_comm],
    exact hfi n },
  refine integrable_of_tendsto_integral_norm hφ _ hfm hfi (h.congr' _),
  filter_upwards [hb₂.eventually (eventually_ge_at_top $ a)],
  intros n hbn,
  rw [interval_integral.integral_of_le hbn, measure.restrict_restrict (hφ.measurable n),
      inter_comm],
  refl
end

end integrable_of_interval_integral

section integral_of_interval_integral

variables {α : Type*} {E : Type*} [topological_space α] [linear_order α] [order_closed_topology α]
  [measurable_space α] [opens_measurable_space α] [measurable_space E]
  [normed_group E] [topological_space.second_countable_topology E] [complete_space E]
  [normed_space ℝ E] [borel_space E] {μ : measure α} {a b : ℕ → α}
  (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (hb₁ : monotone b) {f : α → E} (hfm : measurable f)

include hfm ha₁ hb₁

lemma integral_eq_of_tendsto_interval_integral [no_bot_order α] (I : E)
  (hfi : integrable f μ) (ha₂ : tendsto a at_top at_bot) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ n, ∫ x in a n .. b n, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x, f x ∂μ = I :=
begin
  let φ := λ n, Ioc (a n) (b n),
  have hφ : growing_family μ φ := growing_family_Ioc ha₁ ha₂ hb₁ hb₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b 0)],
  intros n han,
  have : a n ≤ b n := han.trans (hb₁ $ zero_le n),
  exact interval_integral.integral_of_le this
end

omit hb₁

lemma integral_Iic_eq_of_tendsto_interval_integral [no_bot_order α] (I : E) (b : α)
  (hfi : integrable_on f (Iic b) μ) (ha₂ : tendsto a at_top at_bot)
  (h : tendsto (λ n, ∫ x in a n .. b, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x in Iic b, f x ∂μ = I :=
begin
  let φ := λ n, Ioi (a n),
  have hφ : growing_family (μ.restrict $ Iic b) φ := growing_family_Ioi ha₁ ha₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b)],
  intros n han,
  rw [interval_integral.integral_of_le han, measure.restrict_restrict (hφ.measurable n)],
  refl
end

omit ha₁
include hb₁

lemma integral_Ioi_eq_of_tendsto_interval_integral (I : E) (a : α)
  (hfi : integrable_on f (Ioi a) μ) (hb₂ : tendsto b at_top at_top)
  (h : tendsto (λ n, ∫ x in a .. b n, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x in Ioi a, f x ∂μ = I :=
begin
  let φ := λ n, Iic (b n),
  have hφ : growing_family (μ.restrict $ Ioi a) φ := growing_family_Iic hb₁ hb₂,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [hb₂.eventually (eventually_ge_at_top $ a)],
  intros n hbn,
  rw [interval_integral.integral_of_le hbn, measure.restrict_restrict (hφ.measurable n),
      inter_comm],
  refl
end

end integral_of_interval_integral

end measure_theory
