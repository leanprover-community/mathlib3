/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.interval_integral
import order.filter.at_top_bot

open measure_theory filter set
open_locale ennreal nnreal topological_space

namespace measure_theory

section assumed

variables {α : Type*} [measurable_space α] {μ : measure α}

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
  (hf : ∀n, ae_measurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x))
  (h_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 $ F x)) :
  tendsto (λ n, ∫⁻ x, f n x ∂μ) at_top (𝓝 $ ∫⁻ x, F x ∂μ) :=
sorry

end assumed

section ae_cover

variables {α ι : Type*} [preorder ι]
  [measurable_space α] (μ : measure α)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n`, and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `+∞`.

    See for example `measure_theory.set_lintegral_tendsto_lintegral`,
    `measure_theory.integrable_of_set_integral_norm_tendsto` and
    `measure_theory.set_integral_tendsto_integral`. -/
structure ae_cover (φ : ι → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in at_top, x ∈ φ i)
(measurable : ∀ i, measurable_set $ φ i)

variables {μ}

section preorder

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top)

lemma ae_cover_Icc :
  ae_cover μ (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Icc }

lemma ae_cover_Ici :
  ae_cover μ (λ i, Ici $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ici }

lemma ae_cover_Iic :
  ae_cover μ (λ i, Iic $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iic }

end preorder

section linear_order

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top)

lemma ae_cover_Ioo [no_bot_order α] [no_top_order α] :
  ae_cover μ (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioo }

lemma ae_cover_Ioc [no_bot_order α] : ae_cover μ (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioc }

lemma ae_cover_Ico [no_top_order α] : ae_cover μ (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ico }

lemma ae_cover_Ioi [no_bot_order α] :
  ae_cover μ (λ i, Ioi $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ioi }

lemma ae_cover_Iio [no_top_order α] :
  ae_cover μ (λ i, Iio $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iio }

end linear_order

lemma ae_cover.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  {f : α → β} {φ : ι → set α} (hφ : ae_cover μ φ) :
  ∀ᵐ x ∂μ, tendsto (λ i, (φ i).indicator f x) at_top (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

end ae_cover

lemma ae_cover.comp_tendsto_at_top {α ι ι' : Type*} [semilattice_sup ι] [nonempty ι]
  [preorder ι'] [measurable_space α] {μ : measure α} {φ : ι → set α} (hφ : ae_cover μ φ)
  {u : ι' → ι} (hu : tendsto u at_top at_top) :
  ae_cover μ (φ ∘ u) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
  begin
    intros x hx,
    rw eventually_at_top at hx,
    rcases hx with ⟨i, hi⟩,
    exact (hu.eventually (eventually_ge_at_top i)).mono (λ j hij, hi (u j) hij)
  end,
  measurable := λ i, hφ.measurable (u i) }

section ae_cover_Union_Inter_encodable

section preorder_ι

variables {α ι : Type*} [preorder ι] [encodable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bUnion_Iic_ae_cover {φ : ι → set α} (hφ : ae_cover μ φ) :
  ae_cover μ (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    (λ x h, h.mono (λ i hi, mem_bUnion right_mem_Iic hi)),
  measurable := λ i, measurable_set.bUnion (countable_encodable _) (λ n _, hφ.measurable n) }

--move me
lemma bUnion_Iic_mono (φ : ι → set α) :
  monotone (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
λ i j hij, bUnion_subset_bUnion_left (λ k hk, le_trans hk hij)

--move me
lemma subset_bUnion_Iic (φ : ι → set α) (n : ι) :
  φ n ⊆ ⋃ k (h : k ∈ Iic n), φ k :=
subset_bUnion_of_mem right_mem_Iic

end preorder_ι

section linear_order_ι

variables {α ι : Type*} [linear_order ι] [encodable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bInter_Ici_ae_cover [nonempty ι] {φ : ι → set α} (hφ : ae_cover μ φ)
  [nonempty ι] : ae_cover μ (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    begin
      intros x h,
      rw eventually_at_top at *,
      rcases h with ⟨i, hi⟩,
      use i,
      intros j hj,
      exact mem_bInter (λ k hk, hi k (le_trans hj hk)),
    end,
  measurable := λ i, measurable_set.bInter (countable_encodable _) (λ n _, hφ.measurable n) }

--move me
lemma bInter_Ici_mono (φ : ι → set α) :
  monotone (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
λ i j hij, bInter_subset_bInter_left (λ k hk, le_trans hij hk)

--move me
lemma bInter_Ici_subset (φ : ι → set α) (n : ι) :
  (⋂ k (h : k ∈ Ici n), φ k) ⊆ φ n :=
bInter_subset_of_mem left_mem_Ici

end linear_order_ι

end ae_cover_Union_Inter_encodable

section lintegral

variables {α ι : Type*} [measurable_space α] {μ : measure α} [semilattice_sup ι] [nonempty ι]

lemma ae_cover.lintegral_tendsto_of_monotone_of_nat {φ : ℕ → set α} (hφ : ae_cover μ φ)
  (hmono : monotone φ) {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
let F := λ n, (φ n).indicator f in
have key₁ : ∀ n, ae_measurable (F n) μ, from λ n, (hfm.indicator (hφ.measurable n)).ae_measurable,
have key₂ : ∀ᵐ (x : α) ∂μ, monotone (λ n, F n x), from ae_of_all _
  (λ x i j hij, indicator_le_indicator_of_subset (hmono hij) (λ x, zero_le $ f x) x),
have key₃ : ∀ᵐ (x : α) ∂μ, tendsto (λ n, F n x) at_top (𝓝 (f x)), from hφ.ae_tendsto_indicator,
(lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr
  (λ n, lintegral_indicator f (hφ.measurable n))

lemma ae_cover.lintegral_tendsto_of_nat {φ : ℕ → set α} (hφ : ae_cover μ φ)
  {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
begin
  have lim₁ := hφ.bInter_Ici_ae_cover.lintegral_tendsto_of_monotone_of_nat (bInter_Ici_mono φ) hfm,
  have lim₂ := hφ.bUnion_Iic_ae_cover.lintegral_tendsto_of_monotone_of_nat (bUnion_Iic_mono φ) hfm,
  have le₁ := λ n, lintegral_mono_set (bInter_Ici_subset φ n),
  have le₂ := λ n, lintegral_mono_set (subset_bUnion_Iic φ n),
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂
end

lemma ae_cover.lintegral_tendsto_of_at_top_countably_generated {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
htop.tendsto_of_seq_tendsto (λ u hu, (hφ.comp_tendsto_at_top hu).lintegral_tendsto_of_nat hfm)

end lintegral

end measure_theory
