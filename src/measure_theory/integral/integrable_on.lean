/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/

import measure_theory.function.l1_space
import analysis.normed_space.indicator_function

/-! # Functions integrable on a set and at a filter

We define `integrable_on f s μ := integrable f (μ.restrict s)` and prove theorems like
`integrable_on_union : integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ`.

Next we define a predicate `integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ μ.ae` and `μ` is finite
at `l`.

-/

noncomputable theory
open set filter topological_space measure_theory function
open_locale classical topology interval big_operators filter ennreal measure_theory

variables {α β E F : Type*} [measurable_space α]

section

variables [topological_space β] {l l' : filter α} {f g : α → β} {μ ν : measure α}

/-- A function `f` is strongly measurable at a filter `l` w.r.t. a measure `μ` if it is
ae strongly measurable w.r.t. `μ.restrict s` for some `s ∈ l`. -/
def strongly_measurable_at_filter (f : α → β) (l : filter α) (μ : measure α . volume_tac) :=
∃ s ∈ l, ae_strongly_measurable f (μ.restrict s)

@[simp] lemma strongly_measurable_at_bot {f : α → β} : strongly_measurable_at_filter f ⊥ μ :=
⟨∅, mem_bot, by simp⟩

protected lemma strongly_measurable_at_filter.eventually (h : strongly_measurable_at_filter f l μ) :
  ∀ᶠ s in l.small_sets, ae_strongly_measurable f (μ.restrict s) :=
(eventually_small_sets' $ λ s t, ae_strongly_measurable.mono_set).2 h

protected lemma strongly_measurable_at_filter.filter_mono
  (h : strongly_measurable_at_filter f l μ) (h' : l' ≤ l) :
  strongly_measurable_at_filter f l' μ :=
let ⟨s, hsl, hs⟩ := h in ⟨s, h' hsl, hs⟩

protected lemma measure_theory.ae_strongly_measurable.strongly_measurable_at_filter
  (h : ae_strongly_measurable f μ) :
  strongly_measurable_at_filter f l μ :=
⟨univ, univ_mem, by rwa measure.restrict_univ⟩

lemma ae_strongly_measurable.strongly_measurable_at_filter_of_mem
  {s} (h : ae_strongly_measurable f (μ.restrict s)) (hl : s ∈ l) :
  strongly_measurable_at_filter f l μ :=
⟨s, hl, h⟩

protected lemma measure_theory.strongly_measurable.strongly_measurable_at_filter
  (h : strongly_measurable f) :
  strongly_measurable_at_filter f l μ :=
h.ae_strongly_measurable.strongly_measurable_at_filter

end

namespace measure_theory

section normed_add_comm_group

lemma has_finite_integral_restrict_of_bounded [normed_add_comm_group E] {f : α → E} {s : set α}
  {μ : measure α} {C}  (hs : μ s < ∞) (hf : ∀ᵐ x ∂(μ.restrict s), ‖f x‖ ≤ C) :
  has_finite_integral f (μ.restrict s) :=
by haveI : is_finite_measure (μ.restrict s) := ⟨by rwa [measure.restrict_apply_univ]⟩;
  exact has_finite_integral_of_bounded hf

variables [normed_add_comm_group E] {f g : α → E} {s t : set α} {μ ν : measure α}

/-- A function is `integrable_on` a set `s` if it is almost everywhere strongly measurable on `s`
and if the integral of its pointwise norm over `s` is less than infinity. -/
def integrable_on (f : α → E) (s : set α) (μ : measure α . volume_tac) : Prop :=
integrable f (μ.restrict s)

lemma integrable_on.integrable (h : integrable_on f s μ) :
  integrable f (μ.restrict s) := h

@[simp] lemma integrable_on_empty : integrable_on f ∅ μ :=
by simp [integrable_on, integrable_zero_measure]

@[simp] lemma integrable_on_univ : integrable_on f univ μ ↔ integrable f μ :=
by rw [integrable_on, measure.restrict_univ]

lemma integrable_on_zero : integrable_on (λ _, (0:E)) s μ := integrable_zero _ _ _

@[simp] lemma integrable_on_const {C : E} : integrable_on (λ _, C) s μ ↔ C = 0 ∨ μ s < ∞ :=
integrable_const_iff.trans $ by rw [measure.restrict_apply_univ]

lemma integrable_on.mono (h : integrable_on f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono_measure $ measure.restrict_mono hs hμ

lemma integrable_on.mono_set (h : integrable_on f t μ) (hst : s ⊆ t) :
  integrable_on f s μ :=
h.mono hst le_rfl

lemma integrable_on.mono_measure (h : integrable_on f s ν) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono (subset.refl _) hμ

lemma integrable_on.mono_set_ae (h : integrable_on f t μ) (hst : s ≤ᵐ[μ] t) :
  integrable_on f s μ :=
h.integrable.mono_measure $ measure.restrict_mono_ae hst

lemma integrable_on.congr_set_ae (h : integrable_on f t μ) (hst : s =ᵐ[μ] t) :
  integrable_on f s μ :=
h.mono_set_ae hst.le

lemma integrable_on.congr_fun' (h : integrable_on f s μ) (hst : f =ᵐ[μ.restrict s] g) :
  integrable_on g s μ :=
integrable.congr h hst

lemma integrable_on.congr_fun (h : integrable_on f s μ) (hst : eq_on f g s)
  (hs : measurable_set s) :
  integrable_on g s μ :=
h.congr_fun' ((ae_restrict_iff' hs).2 (eventually_of_forall hst))

lemma integrable.integrable_on (h : integrable f μ) : integrable_on f s μ :=
h.mono_measure $ measure.restrict_le_self

lemma integrable.integrable_on' (h : integrable f (μ.restrict s)) : integrable_on f s μ :=
h

lemma integrable_on.restrict (h : integrable_on f s μ) (hs : measurable_set s) :
  integrable_on f s (μ.restrict t) :=
by { rw [integrable_on, measure.restrict_restrict hs], exact h.mono_set (inter_subset_left _ _) }

lemma integrable_on.left_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f s μ :=
h.mono_set $ subset_union_left _ _

lemma integrable_on.right_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f t μ :=
h.mono_set $ subset_union_right _ _

lemma integrable_on.union (hs : integrable_on f s μ) (ht : integrable_on f t μ) :
  integrable_on f (s ∪ t) μ :=
(hs.add_measure ht).mono_measure $ measure.restrict_union_le _ _

@[simp] lemma integrable_on_union :
  integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ :=
⟨λ h, ⟨h.left_of_union, h.right_of_union⟩, λ h, h.1.union h.2⟩

@[simp] lemma integrable_on_singleton_iff {x : α} [measurable_singleton_class α] :
  integrable_on f {x} μ ↔ f x = 0 ∨ μ {x} < ∞ :=
begin
  have : f =ᵐ[μ.restrict {x}] (λ y, f x),
  { filter_upwards [ae_restrict_mem (measurable_set_singleton x)] with _ ha,
    simp only [mem_singleton_iff.1 ha], },
  rw [integrable_on, integrable_congr this, integrable_const_iff],
  simp,
end

@[simp] lemma integrable_on_finite_bUnion {s : set β} (hs : s.finite)
  {t : β → set α} : integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
begin
  apply hs.induction_on,
  { simp },
  { intros a s ha hs hf, simp [hf, or_imp_distrib, forall_and_distrib] }
end

@[simp] lemma integrable_on_finset_Union {s : finset β} {t : β → set α} :
  integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
integrable_on_finite_bUnion s.finite_to_set

@[simp] lemma integrable_on_finite_Union [finite β] {t : β → set α} :
  integrable_on f (⋃ i, t i) μ ↔ ∀ i, integrable_on f (t i) μ :=
by { casesI nonempty_fintype β,
  simpa using @integrable_on_finset_Union _ _ _ _ _ f μ finset.univ t }

lemma integrable_on.add_measure (hμ : integrable_on f s μ) (hν : integrable_on f s ν) :
  integrable_on f s (μ + ν) :=
by { delta integrable_on, rw measure.restrict_add, exact hμ.integrable.add_measure hν }

@[simp] lemma integrable_on_add_measure :
  integrable_on f s (μ + ν) ↔ integrable_on f s μ ∧ integrable_on f s ν :=
⟨λ h, ⟨h.mono_measure (measure.le_add_right le_rfl),
  h.mono_measure (measure.le_add_left le_rfl)⟩,
  λ h, h.1.add_measure h.2⟩

lemma _root_.measurable_embedding.integrable_on_map_iff [measurable_space β] {e : α → β}
  (he : measurable_embedding e) {f : β → E} {μ : measure α} {s : set β} :
  integrable_on f s (measure.map e μ) ↔ integrable_on (f ∘ e) (e ⁻¹' s) μ :=
by simp only [integrable_on, he.restrict_map, he.integrable_map_iff]

lemma integrable_on_map_equiv [measurable_space β] (e : α ≃ᵐ β) {f : β → E} {μ : measure α}
  {s : set β} :
  integrable_on f s (measure.map e μ) ↔ integrable_on (f ∘ e) (e ⁻¹' s) μ :=
by simp only [integrable_on, e.restrict_map, integrable_map_equiv e]

lemma measure_preserving.integrable_on_comp_preimage [measurable_space β] {e : α → β} {ν}
  (h₁ : measure_preserving e μ ν) (h₂ : measurable_embedding e) {f : β → E} {s : set β} :
  integrable_on (f ∘ e) (e ⁻¹' s) μ ↔ integrable_on f s ν :=
(h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

lemma measure_preserving.integrable_on_image [measurable_space β] {e : α → β} {ν}
  (h₁ : measure_preserving e μ ν) (h₂ : measurable_embedding e) {f : β → E} {s : set α} :
  integrable_on f (e '' s) ν ↔  integrable_on (f ∘ e) s μ :=
((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

lemma integrable_indicator_iff (hs : measurable_set s) :
  integrable (indicator s f) μ ↔ integrable_on f s μ :=
by simp [integrable_on, integrable, has_finite_integral, nnnorm_indicator_eq_indicator_nnnorm,
  ennreal.coe_indicator, lintegral_indicator _ hs, ae_strongly_measurable_indicator_iff hs]

lemma integrable_on.integrable_indicator (h : integrable_on f s μ) (hs : measurable_set s) :
  integrable (indicator s f) μ :=
(integrable_indicator_iff hs).2 h

lemma integrable.indicator (h : integrable f μ) (hs : measurable_set s) :
  integrable (indicator s f) μ :=
h.integrable_on.integrable_indicator hs

lemma integrable_on.indicator (h : integrable_on f s μ) (ht : measurable_set t) :
  integrable_on (indicator t f) s μ :=
integrable.indicator h ht

lemma integrable_indicator_const_Lp {E} [normed_add_comm_group E]
  {p : ℝ≥0∞} {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) :
  integrable (indicator_const_Lp p hs hμs c) μ :=
begin
  rw [integrable_congr indicator_const_Lp_coe_fn, integrable_indicator_iff hs, integrable_on,
    integrable_const_iff, lt_top_iff_ne_top],
  right,
  simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply] using hμs,
end

/-- If a function is integrable on a set `s` and nonzero there, then the measurable hull of `s` is
well behaved: the restriction of the measure to `to_measurable μ s` coincides with its restriction
to `s`. -/
lemma integrable_on.restrict_to_measurable (hf : integrable_on f s μ) (h's : ∀ x ∈ s, f x ≠ 0) :
  μ.restrict (to_measurable μ s) = μ.restrict s :=
begin
  rcases exists_seq_strict_anti_tendsto (0 : ℝ) with ⟨u, u_anti, u_pos, u_lim⟩,
  let v := λ n, to_measurable (μ.restrict s) {x | u n ≤ ‖f x‖},
  have A : ∀ n, μ (s ∩ v n) ≠ ∞,
  { assume n,
    rw [inter_comm, ← measure.restrict_apply (measurable_set_to_measurable _ _),
      measure_to_measurable],
    exact (hf.measure_ge_lt_top (u_pos n)).ne },
  apply measure.restrict_to_measurable_of_cover _ A,
  assume x hx,
  have : 0 < ‖f x‖, by simp only [h's x hx, norm_pos_iff, ne.def, not_false_iff],
  obtain ⟨n, hn⟩ : ∃ n, u n < ‖f x‖, from ((tendsto_order.1 u_lim).2 _ this).exists,
  refine mem_Union.2 ⟨n, _⟩,
  exact subset_to_measurable _ _ hn.le
end

/-- If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is integrable on `t`
if `t` is null-measurable. -/
lemma integrable_on.of_ae_diff_eq_zero (hf : integrable_on f s μ)
  (ht : null_measurable_set t μ) (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) :
  integrable_on f t μ :=
begin
  let u := {x ∈ s | f x ≠ 0},
  have hu : integrable_on f u μ := hf.mono_set (λ x hx, hx.1),
  let v := to_measurable μ u,
  have A : integrable_on f v μ,
  { rw [integrable_on, hu.restrict_to_measurable],
    { exact hu },
    { assume x hx, exact hx.2 } },
  have B : integrable_on f (t \ v) μ,
  { apply integrable_on_zero.congr,
    filter_upwards [ae_restrict_of_ae h't, ae_restrict_mem₀
      (ht.diff (measurable_set_to_measurable μ u).null_measurable_set)] with x hxt hx,
    by_cases h'x : x ∈ s,
    { by_contra H,
      exact hx.2 (subset_to_measurable μ u ⟨h'x, ne.symm H⟩) },
    { exact (hxt ⟨hx.1, h'x⟩).symm, } },
  apply (A.union B).mono_set _,
  rw union_diff_self,
  exact subset_union_right _ _
end

/-- If a function is integrable on a set `s`, and vanishes on `t \ s`, then it is integrable on `t`
if `t` is measurable. -/
lemma integrable_on.of_forall_diff_eq_zero (hf : integrable_on f s μ)
  (ht : measurable_set t) (h't : ∀ x ∈ t \ s, f x = 0) :
  integrable_on f t μ :=
hf.of_ae_diff_eq_zero ht.null_measurable_set (eventually_of_forall h't)

/-- If a function is integrable on a set `s` and vanishes almost everywhere on its complement,
then it is integrable. -/
lemma integrable_on.integrable_of_ae_not_mem_eq_zero (hf : integrable_on f s μ)
  (h't : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : integrable f μ :=
begin
  rw ← integrable_on_univ,
  apply hf.of_ae_diff_eq_zero null_measurable_set_univ,
  filter_upwards [h't] with x hx h'x using hx h'x.2,
end

/-- If a function is integrable on a set `s` and vanishes everywhere on its complement,
then it is integrable. -/
lemma integrable_on.integrable_of_forall_not_mem_eq_zero (hf : integrable_on f s μ)
  (h't : ∀ x ∉ s, f x = 0) : integrable f μ :=
hf.integrable_of_ae_not_mem_eq_zero (eventually_of_forall (λ x hx, h't x hx))

lemma integrable_on_iff_integrable_of_support_subset (h1s : support f ⊆ s) :
  integrable_on f s μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, λ h, h.integrable_on⟩,
  apply h.integrable_of_forall_not_mem_eq_zero (λ x hx, _),
  contrapose! hx,
  exact h1s (mem_support.2 hx),
end

lemma integrable_on_Lp_of_measure_ne_top {E} [normed_add_comm_group E]
  {p : ℝ≥0∞} {s : set α} (f : Lp E p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) :
  integrable_on f s μ :=
begin
  refine mem_ℒp_one_iff_integrable.mp _,
  have hμ_restrict_univ : (μ.restrict s) set.univ < ∞,
    by simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply, lt_top_iff_ne_top],
  haveI hμ_finite : is_finite_measure (μ.restrict s) := ⟨hμ_restrict_univ⟩,
  exact ((Lp.mem_ℒp _).restrict s).mem_ℒp_of_exponent_le hp,
end

lemma integrable.lintegral_lt_top {f : α → ℝ} (hf : integrable f μ) :
  ∫⁻ x, ennreal.of_real (f x) ∂μ < ∞ :=
calc ∫⁻ x, ennreal.of_real (f x) ∂μ
    ≤ ∫⁻ x, ↑‖f x‖₊ ∂μ : lintegral_of_real_le_lintegral_nnnorm f
... < ∞ : hf.2

lemma integrable_on.set_lintegral_lt_top {f : α → ℝ} {s : set α} (hf : integrable_on f s μ) :
  ∫⁻ x in s, ennreal.of_real (f x) ∂μ < ∞ :=
integrable.lintegral_lt_top hf

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.small_sets`. -/
def integrable_at_filter (f : α → E) (l : filter α) (μ : measure α . volume_tac) :=
∃ s ∈ l, integrable_on f s μ

variables {l l' : filter α}

lemma integrable.integrable_at_filter (h : integrable f μ) (l : filter α) :
  integrable_at_filter f l μ :=
⟨univ, filter.univ_mem, integrable_on_univ.2 h⟩

protected lemma integrable_at_filter.eventually (h : integrable_at_filter f l μ) :
  ∀ᶠ s in l.small_sets, integrable_on f s μ :=
iff.mpr (eventually_small_sets' $ λ s t hst ht, ht.mono_set hst) h

lemma integrable_at_filter.filter_mono (hl : l ≤ l') (hl' : integrable_at_filter f l' μ) :
  integrable_at_filter f l μ :=
let ⟨s, hs, hsf⟩ := hl' in ⟨s, hl hs, hsf⟩

lemma integrable_at_filter.inf_of_left (hl : integrable_at_filter f l μ) :
  integrable_at_filter f (l ⊓ l') μ :=
hl.filter_mono inf_le_left

lemma integrable_at_filter.inf_of_right (hl : integrable_at_filter f l μ) :
  integrable_at_filter f (l' ⊓ l) μ :=
hl.filter_mono inf_le_right

@[simp] lemma integrable_at_filter.inf_ae_iff {l : filter α} :
  integrable_at_filter f (l ⊓ μ.ae) μ ↔ integrable_at_filter f l μ :=
begin
  refine ⟨_, λ h, h.filter_mono inf_le_left⟩,
  rintros ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩,
  refine ⟨t, ht, _⟩,
  refine hf.integrable.mono_measure (λ v hv, _),
  simp only [measure.restrict_apply hv],
  refine measure_mono_ae (mem_of_superset hu $ λ x hx, _),
  exact λ ⟨hv, ht⟩, ⟨hv, ⟨ht, hx⟩⟩
end

alias integrable_at_filter.inf_ae_iff ↔ integrable_at_filter.of_inf_ae _

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
lemma measure.finite_at_filter.integrable_at_filter {l : filter α} [is_measurably_generated l]
  (hfm : strongly_measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  (hf : l.is_bounded_under (≤) (norm ∘ f)) :
  integrable_at_filter f l μ :=
begin
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ s in l.small_sets, ∀ x ∈ s, ‖f x‖ ≤ C,
    from hf.imp (λ C hC, eventually_small_sets.2 ⟨_, hC, λ t, id⟩),
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_small_sets
    with ⟨s, hsl, hsm, hfm, hμ, hC⟩,
  refine ⟨s, hsl, ⟨hfm, has_finite_integral_restrict_of_bounded hμ _⟩⟩,
  exact C,
  rw [ae_restrict_eq hsm, eventually_inf_principal],
  exact eventually_of_forall hC
end

lemma measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
  {l : filter α} [is_measurably_generated l] (hfm : strongly_measurable_at_filter f l μ)
  (hμ : μ.finite_at_filter l) {b} (hf : tendsto f (l ⊓ μ.ae) (𝓝 b)) :
  integrable_at_filter f l μ :=
(hμ.inf_of_left.integrable_at_filter (hfm.filter_mono inf_le_left)
  hf.norm.is_bounded_under_le).of_inf_ae

alias measure.finite_at_filter.integrable_at_filter_of_tendsto_ae ←
  _root_.filter.tendsto.integrable_at_filter_ae

lemma measure.finite_at_filter.integrable_at_filter_of_tendsto {l : filter α}
  [is_measurably_generated l] (hfm : strongly_measurable_at_filter f l μ)
  (hμ : μ.finite_at_filter l) {b} (hf : tendsto f l (𝓝 b)) :
  integrable_at_filter f l μ :=
hμ.integrable_at_filter hfm hf.norm.is_bounded_under_le

alias measure.finite_at_filter.integrable_at_filter_of_tendsto ←
  _root_.filter.tendsto.integrable_at_filter

lemma integrable_add_of_disjoint {f g : α → E}
  (h : disjoint (support f) (support g)) (hf : strongly_measurable f) (hg : strongly_measurable g) :
  integrable (f + g) μ ↔ integrable f μ ∧ integrable g μ :=
begin
  refine ⟨λ hfg, ⟨_, _⟩, λ h, h.1.add h.2⟩,
  { rw ← indicator_add_eq_left h, exact hfg.indicator hf.measurable_set_support },
  { rw ← indicator_add_eq_right h, exact hfg.indicator hg.measurable_set_support }
end

end normed_add_comm_group

end measure_theory

open measure_theory

variables [normed_add_comm_group E]

/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
lemma continuous_on.ae_measurable [topological_space α] [opens_measurable_space α]
  [measurable_space β] [topological_space β] [borel_space β]
  {f : α → β} {s : set α} {μ : measure α} (hf : continuous_on f s) (hs : measurable_set s) :
  ae_measurable f (μ.restrict s) :=
begin
  nontriviality α, inhabit α,
  have : piecewise s f (λ _, f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs,
  refine ⟨piecewise s f (λ _, f default), _, this.symm⟩,
  apply measurable_of_is_open,
  assume t ht,
  obtain ⟨u, u_open, hu⟩ : ∃ (u : set α), is_open u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    _root_.continuous_on_iff'.1 hf t ht,
  rw [piecewise_preimage, set.ite, hu],
  exact (u_open.measurable_set.inter hs).union ((measurable_const ht.measurable_set).diff hs)
end

/-- A function which is continuous on a separable set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
lemma continuous_on.ae_strongly_measurable_of_is_separable
  [topological_space α] [pseudo_metrizable_space α] [opens_measurable_space α]
  [topological_space β] [pseudo_metrizable_space β]
  {f : α → β} {s : set α} {μ : measure α} (hf : continuous_on f s) (hs : measurable_set s)
  (h's : topological_space.is_separable s) :
  ae_strongly_measurable f (μ.restrict s) :=
begin
  letI := pseudo_metrizable_space_pseudo_metric α,
  borelize β,
  rw ae_strongly_measurable_iff_ae_measurable_separable,
  refine ⟨hf.ae_measurable hs, f '' s, hf.is_separable_image h's, _⟩,
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _),
end

/-- A function which is continuous on a set `s` is almost everywhere strongly measurable with
respect to `μ.restrict s` when either the source space or the target space is second-countable. -/
lemma continuous_on.ae_strongly_measurable
  [topological_space α] [topological_space β] [h : second_countable_topology_either α β]
  [opens_measurable_space α] [pseudo_metrizable_space β]
  {f : α → β} {s : set α} {μ : measure α} (hf : continuous_on f s) (hs : measurable_set s) :
  ae_strongly_measurable f (μ.restrict s) :=
begin
  borelize β,
  refine ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨hf.ae_measurable hs, f '' s, _,
    mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩,
  casesI h.out,
  { let f' : s → β := s.restrict f,
    have A : continuous f' := continuous_on_iff_continuous_restrict.1 hf,
    have B : is_separable (univ : set s) := is_separable_of_separable_space _,
    convert is_separable.image B A using 1,
    ext x,
    simp },
  { exact is_separable_of_separable_space _ }
end

/-- A function which is continuous on a compact set `s` is almost everywhere strongly measurable
with respect to `μ.restrict s`. -/
lemma continuous_on.ae_strongly_measurable_of_is_compact
  [topological_space α] [opens_measurable_space α] [topological_space β] [pseudo_metrizable_space β]
  {f : α → β} {s : set α} {μ : measure α}
  (hf : continuous_on f s) (hs : is_compact s) (h's : measurable_set s) :
  ae_strongly_measurable f (μ.restrict s) :=
begin
  letI := pseudo_metrizable_space_pseudo_metric β,
  borelize β,
  rw ae_strongly_measurable_iff_ae_measurable_separable,
  refine ⟨hf.ae_measurable h's, f '' s, _, _⟩,
  { exact (hs.image_of_continuous_on hf).is_separable },
  { exact mem_of_superset (self_mem_ae_restrict h's) (subset_preimage_image _ _) }
end

lemma continuous_on.integrable_at_nhds_within_of_is_separable
  [topological_space α] [pseudo_metrizable_space α]
  [opens_measurable_space α] {μ : measure α} [is_locally_finite_measure μ]
  {a : α} {t : set α} {f : α → E} (hft : continuous_on f t) (ht : measurable_set t)
  (h't : topological_space.is_separable t) (ha : a ∈ t) :
  integrable_at_filter f (𝓝[t] a) μ :=
begin
  haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _,
  exact (hft a ha).integrable_at_filter ⟨_, self_mem_nhds_within,
    hft.ae_strongly_measurable_of_is_separable ht h't⟩ (μ.finite_at_nhds_within _ _),
end

lemma continuous_on.integrable_at_nhds_within
  [topological_space α] [second_countable_topology_either α E]
  [opens_measurable_space α] {μ : measure α} [is_locally_finite_measure μ]
  {a : α} {t : set α} {f : α → E} (hft : continuous_on f t) (ht : measurable_set t) (ha : a ∈ t) :
  integrable_at_filter f (𝓝[t] a) μ :=
begin
  haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _,
  exact (hft a ha).integrable_at_filter ⟨_, self_mem_nhds_within, hft.ae_strongly_measurable ht⟩
    (μ.finite_at_nhds_within _ _),
end

lemma continuous.integrable_at_nhds
  [topological_space α] [second_countable_topology_either α E]
  [opens_measurable_space α] {μ : measure α} [is_locally_finite_measure μ]
  {f : α → E} (hf : continuous f) (a : α) :
  integrable_at_filter f (𝓝 a) μ :=
begin
  rw ← nhds_within_univ,
  exact hf.continuous_on.integrable_at_nhds_within measurable_set.univ (mem_univ a),
end

/-- If a function is continuous on an open set `s`, then it is strongly measurable at the filter
`𝓝 x` for all `x ∈ s` if either the source space or the target space is second-countable. -/
lemma continuous_on.strongly_measurable_at_filter [topological_space α]
  [opens_measurable_space α] [topological_space β] [pseudo_metrizable_space β]
  [second_countable_topology_either α β] {f : α → β} {s : set α} {μ : measure α}
  (hs : is_open s) (hf : continuous_on f s) :
  ∀ x ∈ s, strongly_measurable_at_filter f (𝓝 x) μ :=
λ x hx, ⟨s, is_open.mem_nhds hs hx, hf.ae_strongly_measurable hs.measurable_set⟩

lemma continuous_at.strongly_measurable_at_filter
  [topological_space α] [opens_measurable_space α] [second_countable_topology_either α E]
  {f : α → E} {s : set α} {μ : measure α} (hs : is_open s) (hf : ∀ x ∈ s, continuous_at f x) :
  ∀ x ∈ s, strongly_measurable_at_filter f (𝓝 x) μ :=
continuous_on.strongly_measurable_at_filter hs $ continuous_at.continuous_on hf

lemma continuous.strongly_measurable_at_filter [topological_space α] [opens_measurable_space α]
  [topological_space β] [pseudo_metrizable_space β] [second_countable_topology_either α β]
  {f : α → β} (hf : continuous f) (μ : measure α) (l : filter α) :
  strongly_measurable_at_filter f l μ :=
hf.strongly_measurable.strongly_measurable_at_filter

/-- If a function is continuous on a measurable set `s`, then it is measurable at the filter
  `𝓝[s] x` for all `x`. -/
lemma continuous_on.strongly_measurable_at_filter_nhds_within {α β : Type*} [measurable_space α]
  [topological_space α] [opens_measurable_space α] [topological_space β] [pseudo_metrizable_space β]
  [second_countable_topology_either α β] {f : α → β} {s : set α} {μ : measure α}
  (hf : continuous_on f s) (hs : measurable_set s) (x : α) :
  strongly_measurable_at_filter f (𝓝[s] x) μ :=
⟨s, self_mem_nhds_within, hf.ae_strongly_measurable hs⟩
