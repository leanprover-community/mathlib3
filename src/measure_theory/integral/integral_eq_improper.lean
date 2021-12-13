/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.integral.interval_integral
import order.filter.at_top_bot

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `measure_theory.ae_cover`. It is a rather technical
definition whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a
countably generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable
space `α` equipped with a measure `μ`, one should think of a hypothesis `hφ : ae_cover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit
of `∫ x in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often,
one should not try too hard to use a `ae_cover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto` where we use `(λ x, Ioi x)`
as an `ae_cover` w.r.t. `μ.restrict (Iic b)`, instead of using `(λ x, Ioc x b)`.

## Main statements

- `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is a measurable `ennreal`-valued function,
  then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`
- `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, if `f` is measurable and integrable on each `φ n`,
  and if `∫ x in φ n, ∥f x∥ ∂μ` tends to some `I : ℝ` as n tends to `l`, then `f` is integrable
- `measure_theory.ae_cover.integral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is measurable and integrable (globally),
  then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis.
-/

open measure_theory filter set topological_space
open_locale ennreal nnreal topological_space

namespace measure_theory

section ae_cover

variables {α ι : Type*} [measurable_space α] (μ : measure α) (l : filter ι)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ` and a filter `l`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.

    See for example `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated`,
    `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` and
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
structure ae_cover (φ : ι → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ φ i)
(measurable : ∀ i, measurable_set $ φ i)

variables {μ} {l}

section preorder_α

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)

lemma ae_cover_Icc :
  ae_cover μ l (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Icc }

lemma ae_cover_Ici :
  ae_cover μ l (λ i, Ici $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ici }

lemma ae_cover_Iic :
  ae_cover μ l (λ i, Iic $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iic }

end preorder_α

section linear_order_α

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)

lemma ae_cover_Ioo [no_bot_order α] [no_top_order α] :
  ae_cover μ l (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioo }

lemma ae_cover_Ioc [no_bot_order α] : ae_cover μ l (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioc }

lemma ae_cover_Ico [no_top_order α] : ae_cover μ l (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ico }

lemma ae_cover_Ioi [no_bot_order α] :
  ae_cover μ l (λ i, Ioi $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ioi }

lemma ae_cover_Iio [no_top_order α] :
  ae_cover μ l (λ i, Iio $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iio }

end linear_order_α

lemma ae_cover.restrict {φ : ι → set α} (hφ : ae_cover μ l φ) {s : set α} :
  ae_cover (μ.restrict s) l φ :=
{ ae_eventually_mem := ae_restrict_of_ae hφ.ae_eventually_mem,
  measurable := hφ.measurable }

lemma ae_cover_restrict_of_ae_imp {s : set α} {φ : ι → set α}
  (hs : measurable_set s) (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in l, x ∈ φ n)
  (measurable : ∀ n, measurable_set $ φ n) :
  ae_cover (μ.restrict s) l φ :=
{ ae_eventually_mem := by rwa ae_restrict_iff' hs,
  measurable := measurable }

lemma ae_cover.inter_restrict {φ : ι → set α} (hφ : ae_cover μ l φ)
  {s : set α} (hs : measurable_set s) :
  ae_cover (μ.restrict s) l (λ i, φ i ∩ s) :=
ae_cover_restrict_of_ae_imp hs
  (hφ.ae_eventually_mem.mono (λ x hx hxs, hx.mono $ λ i hi, ⟨hi, hxs⟩))
  (λ i, (hφ.measurable i).inter hs)

lemma ae_cover.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  {f : α → β} {φ : ι → set α} (hφ : ae_cover μ l φ) :
  ∀ᵐ x ∂μ, tendsto (λ i, (φ i).indicator f x) l (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

end ae_cover

lemma ae_cover.comp_tendsto {α ι ι' : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  {l' : filter ι'} {φ : ι → set α} (hφ : ae_cover μ l φ)
  {u : ι' → ι} (hu : tendsto u l' l) :
  ae_cover μ l' (φ ∘ u) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono (λ x hx, hu.eventually hx),
  measurable := λ i, hφ.measurable (u i) }

section ae_cover_Union_Inter_encodable

variables {α ι : Type*} [encodable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bUnion_Iic_ae_cover [preorder ι] {φ : ι → set α} (hφ : ae_cover μ at_top φ) :
  ae_cover μ at_top (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    (λ x h, h.mono (λ i hi, mem_bUnion right_mem_Iic hi)),
  measurable := λ i, measurable_set.bUnion (countable_encodable _) (λ n _, hφ.measurable n) }

lemma ae_cover.bInter_Ici_ae_cover [semilattice_sup ι] [nonempty ι] {φ : ι → set α}
  (hφ : ae_cover μ at_top φ) : ae_cover μ at_top (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
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

end ae_cover_Union_Inter_encodable

section lintegral

variables {α ι : Type*} [measurable_space α] {μ : measure α} {l : filter ι}

private lemma lintegral_tendsto_of_monotone_of_nat {φ : ℕ → set α}
  (hφ : ae_cover μ at_top φ) (hmono : monotone φ) {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
let F := λ n, (φ n).indicator f in
have key₁ : ∀ n, ae_measurable (F n) μ, from λ n, hfm.indicator (hφ.measurable n),
have key₂ : ∀ᵐ (x : α) ∂μ, monotone (λ n, F n x), from ae_of_all _
  (λ x i j hij, indicator_le_indicator_of_subset (hmono hij) (λ x, zero_le $ f x) x),
have key₃ : ∀ᵐ (x : α) ∂μ, tendsto (λ n, F n x) at_top (𝓝 (f x)), from hφ.ae_tendsto_indicator,
(lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr
  (λ n, lintegral_indicator f (hφ.measurable n))

lemma ae_cover.lintegral_tendsto_of_nat {φ : ℕ → set α} (hφ : ae_cover μ at_top φ)
  {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
begin
  have lim₁ := lintegral_tendsto_of_monotone_of_nat (hφ.bInter_Ici_ae_cover)
    (λ i j hij, bInter_subset_bInter_left (Ici_subset_Ici.mpr hij)) hfm,
  have lim₂ := lintegral_tendsto_of_monotone_of_nat (hφ.bUnion_Iic_ae_cover)
    (λ i j hij, bUnion_subset_bUnion_left (Iic_subset_Iic.mpr hij)) hfm,
  have le₁ := λ n, lintegral_mono_set (bInter_subset_of_mem left_mem_Ici),
  have le₂ := λ n, lintegral_mono_set (subset_bUnion_of_mem right_mem_Iic),
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂
end

lemma ae_cover.lintegral_tendsto_of_countably_generated {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → ℝ≥0∞}
  (hfm : ae_measurable f μ) : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) l (𝓝 $ ∫⁻ x, f x ∂μ) :=
hcg.tendsto_of_seq_tendsto (λ u hu, (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm)

lemma ae_cover.lintegral_eq_of_tendsto [l.ne_bot] {φ : ι → set α} (hφ : ae_cover μ l φ)
  (hcg : l.is_countably_generated) {f : α → ℝ≥0∞} (I : ℝ≥0∞)
  (hfm : ae_measurable f μ) (htendsto : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hcg hfm) htendsto

lemma ae_cover.supr_lintegral_eq_of_countably_generated [nonempty ι] [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → ℝ≥0∞}
  (hfm : ae_measurable f μ) : (⨆ (i : ι), ∫⁻ x in φ i, f x ∂μ) = ∫⁻ x, f x ∂μ :=
begin
  have := hφ.lintegral_tendsto_of_countably_generated hcg hfm,
  refine csupr_eq_of_forall_le_of_forall_lt_exists_gt
    (λ i, lintegral_mono' measure.restrict_le_self (le_refl _)) (λ w hw, _),
  rcases exists_between hw with ⟨m, hm₁, hm₂⟩,
  rcases (eventually_ge_of_tendsto_gt hm₂ this).exists with ⟨i, hi⟩,
  exact ⟨i, lt_of_lt_of_le hm₁ hi⟩,
end

end lintegral

section integrable

variables {α ι E : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  [normed_group E] [measurable_space E] [opens_measurable_space E]

lemma ae_cover.integrable_of_lintegral_nnnorm_tendsto [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → E} (I : ℝ)
  (hfm : ae_measurable f μ)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) l (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm, _⟩,
  unfold has_finite_integral,
  rw hφ.lintegral_eq_of_tendsto hcg _ (measurable_nnnorm.comp_ae_measurable hfm).coe_nnreal_ennreal
    htendsto,
  exact ennreal.of_real_lt_top
end

lemma ae_cover.integrable_of_lintegral_nnnorm_tendsto' [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → E} (I : ℝ≥0)
  (hfm : ae_measurable f μ)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) l (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
hφ.integrable_of_lintegral_nnnorm_tendsto hcg I hfm htendsto

lemma ae_cover.integrable_of_integral_norm_tendsto [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → E}
  (I : ℝ) (hfm : ae_measurable f μ) (hfi : ∀ i, integrable_on f (φ i) μ)
  (htendsto : tendsto (λ i, ∫ x in φ i, ∥f x∥ ∂μ) l (𝓝 I)) :
  integrable f μ :=
begin
  refine hφ.integrable_of_lintegral_nnnorm_tendsto hcg I hfm _,
  conv at htendsto in (integral _ _)
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x)))
    hfm.norm.restrict },
  conv at htendsto in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  convert ennreal.tendsto_of_real htendsto,
  ext i : 1,
  rw ennreal.of_real_to_real _,
  exact ne_top_of_lt (hfi i).2
end

lemma ae_cover.integrable_of_integral_tendsto_of_nonneg_ae [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → ℝ} (I : ℝ)
  (hfm : ae_measurable f μ) (hfi : ∀ i, integrable_on f (φ i) μ) (hnng : ∀ᵐ x ∂μ, 0 ≤ f x)
  (htendsto : tendsto (λ i, ∫ x in φ i, f x ∂μ) l (𝓝 I)) :
  integrable f μ :=
hφ.integrable_of_integral_norm_tendsto hcg I hfm hfi
  (htendsto.congr $ λ i, integral_congr_ae $ ae_restrict_of_ae $ hnng.mono $
    λ x hx, (real.norm_of_nonneg hx).symm)

end integrable

section integral

variables {α ι E : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [complete_space E] [second_countable_topology E]

lemma ae_cover.integral_tendsto_of_countably_generated {φ : ι → set α} (hφ : ae_cover μ l φ)
  (hcg : l.is_countably_generated) {f : α → E} (hfm : ae_measurable f μ)
  (hfi : integrable f μ) :
  tendsto (λ i, ∫ x in φ i, f x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
suffices h : tendsto (λ i, ∫ (x : α), (φ i).indicator f x ∂μ) l (𝓝 (∫ (x : α), f x ∂μ)),
by { convert h, ext n, rw integral_indicator (hφ.measurable n) },
tendsto_integral_filter_of_dominated_convergence (λ x, ∥f x∥) hcg
  (eventually_of_forall $ λ i, hfm.indicator $ hφ.measurable i) hfm
  (eventually_of_forall $ λ i, ae_of_all _ $ λ x, norm_indicator_le_norm_self _ _)
  hfi.norm hφ.ae_tendsto_indicator

/-- Slight reformulation of
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
lemma ae_cover.integral_eq_of_tendsto [l.ne_bot] {φ : ι → set α} (hφ : ae_cover μ l φ)
  (hcg : l.is_countably_generated) {f : α → E}
  (I : E) (hfm : ae_measurable f μ) (hfi : integrable f μ)
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hcg hfm hfi) h

lemma ae_cover.integral_eq_of_tendsto_of_nonneg_ae [l.ne_bot] {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hcg : l.is_countably_generated) {f : α → ℝ} (I : ℝ)
  (hnng : 0 ≤ᵐ[μ] f) (hfm : ae_measurable f μ) (hfi : ∀ n, integrable_on f (φ n) μ)
  (htendsto : tendsto (λ n, ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from hφ.integrable_of_integral_tendsto_of_nonneg_ae hcg I hfm hfi hnng htendsto,
hφ.integral_eq_of_tendsto hcg I hfm hfi' htendsto

end integral

section integrable_of_interval_integral

variables {α ι E : Type*}
          [topological_space α] [linear_order α] [order_closed_topology α]
          [measurable_space α] [opens_measurable_space α] {μ : measure α}
          {l : filter ι} [filter.ne_bot l] (hcg : l.is_countably_generated)
          [measurable_space E] [normed_group E] [borel_space E]
          {a b : ι → α} {f : α → E} (hfm : ae_measurable f μ)

include hcg hfm

lemma integrable_of_interval_integral_norm_tendsto [no_bot_order α] [nonempty α]
  (I : ℝ) (hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)
  (h : tendsto (λ i, ∫ x in a i .. b i, ∥f x∥ ∂μ) l (𝓝 $ I)) :
  integrable f μ :=
begin
  let φ := λ n, Ioc (a n) (b n),
  let c : α := classical.choice ‹_›,
  have hφ : ae_cover μ l φ := ae_cover_Ioc ha hb,
  refine hφ.integrable_of_integral_norm_tendsto hcg _ hfm hfi (h.congr' _),
  filter_upwards [ha.eventually (eventually_le_at_bot c), hb.eventually (eventually_ge_at_top c)],
  intros i hai hbi,
  exact interval_integral.integral_of_le (hai.trans hbi)
end

lemma integrable_on_Iic_of_interval_integral_norm_tendsto [no_bot_order α] (I : ℝ) (b : α)
  (hfi : ∀ i, integrable_on f (Ioc (a i) b) μ) (ha : tendsto a l at_bot)
  (h : tendsto (λ i, ∫ x in a i .. b, ∥f x∥ ∂μ) l (𝓝 $ I)) :
  integrable_on f (Iic b) μ :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : ae_cover (μ.restrict $ Iic b) l φ := ae_cover_Ioi ha,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Iic b),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i)],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_tendsto hcg _ hfm.restrict hfi (h.congr' _),
  filter_upwards [ha.eventually (eventually_le_at_bot b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

lemma integrable_on_Ioi_of_interval_integral_norm_tendsto (I : ℝ) (a : α)
  (hfi : ∀ i, integrable_on f (Ioc a (b i)) μ) (hb : tendsto b l at_top)
  (h : tendsto (λ i, ∫ x in a .. b i, ∥f x∥ ∂μ) l (𝓝 $ I)) :
  integrable_on f (Ioi a) μ :=
begin
  let φ := λ i, Iic (b i),
  have hφ : ae_cover (μ.restrict $ Ioi a) l φ := ae_cover_Iic hb,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Ioi a),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i), inter_comm],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_tendsto hcg _ hfm.restrict hfi (h.congr' _),
  filter_upwards [hb.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integrable_of_interval_integral

section integral_of_interval_integral

variables {α ι E : Type*}
          [topological_space α] [linear_order α] [order_closed_topology α]
          [measurable_space α] [opens_measurable_space α] {μ : measure α}
          {l : filter ι} (hcg : l.is_countably_generated)
          [measurable_space E] [normed_group E] [normed_space ℝ E] [borel_space E]
          [complete_space E] [second_countable_topology E]
          {a b : ι → α} {f : α → E} (hfm : ae_measurable f μ)

include hcg hfm

lemma interval_integral_tendsto_integral [no_bot_order α] [nonempty α]
  (hfi : integrable f μ) (ha : tendsto a l at_bot) (hb : tendsto b l at_top) :
  tendsto (λ i, ∫ x in a i .. b i, f x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
begin
  let φ := λ i, Ioc (a i) (b i),
  let c : α := classical.choice ‹_›,
  have hφ : ae_cover μ l φ := ae_cover_Ioc ha hb,
  refine (hφ.integral_tendsto_of_countably_generated hcg hfm hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot c), hb.eventually (eventually_ge_at_top c)],
  intros i hai hbi,
  exact (interval_integral.integral_of_le (hai.trans hbi)).symm
end

lemma interval_integral_tendsto_integral_Iic [no_bot_order α] (b : α)
  (hfi : integrable_on f (Iic b) μ) (ha : tendsto a l at_bot) :
  tendsto (λ i, ∫ x in a i .. b, f x ∂μ) l (𝓝 $ ∫ x in Iic b, f x ∂μ) :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : ae_cover (μ.restrict $ Iic b) l φ := ae_cover_Ioi ha,
  refine (hφ.integral_tendsto_of_countably_generated hcg hfm.restrict hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot $ b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

lemma interval_integral_tendsto_integral_Ioi (a : α)
  (hfi : integrable_on f (Ioi a) μ) (hb : tendsto b l at_top) :
  tendsto (λ i, ∫ x in a .. b i, f x ∂μ) l (𝓝 $ ∫ x in Ioi a, f x ∂μ) :=
begin
  let φ := λ i, Iic (b i),
  have hφ : ae_cover (μ.restrict $ Ioi a) l φ := ae_cover_Iic hb,
  refine (hφ.integral_tendsto_of_countably_generated hcg hfm.restrict hfi).congr' _,
  filter_upwards [hb.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integral_of_interval_integral

end measure_theory
