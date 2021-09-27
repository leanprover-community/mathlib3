/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import measure_theory.integral.integrable_on
import measure_theory.integral.bochner
import order.filter.indicator_function

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We use the property `integrable_on f s μ := integrable f (μ.restrict s)`, defined in
`measure_theory.integrable_on`. We also defined in that same file a predicate
`integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `filter.tendsto.integral_sub_linear_is_o_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.lift' powerset`, i.e. for any `ε>0` there exists `t ∈ l` such that
`∥∫ x in s, f x ∂μ - μ s • c∥ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ a in s, f a ∂μ` is `measure_theory.integral (μ.restrict s) f`
* `∫ a in s, f a` is `∫ a in s, f a ∂volume`

Note that the set notations are defined in the file `measure_theory/integral/bochner`,
but we reference them here because all theorems about set integrals are in this file.

-/

noncomputable theory
open set filter topological_space measure_theory function
open_locale classical topological_space interval big_operators filter ennreal nnreal measure_theory

variables {α β E F : Type*} [measurable_space α]

namespace measure_theory

section normed_group

variables [normed_group E] [measurable_space E] {f g : α → E} {s t : set α} {μ ν : measure α}
  {l l' : filter α} [borel_space E] [second_countable_topology E]

variables [complete_space E] [normed_space ℝ E]

lemma set_integral_congr_ae (hs : measurable_set s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
integral_congr_ae ((ae_restrict_iff' hs).2 h)

lemma set_integral_congr (hs : measurable_set s) (h : eq_on f g s) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
set_integral_congr_ae hs $ eventually_of_forall h

lemma set_integral_congr_set_ae (hst : s =ᵐ[μ] t) :
  ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ :=
by rw restrict_congr_set hst

lemma integral_union (hst : disjoint s t) (hs : measurable_set s) (ht : measurable_set t)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
by simp only [integrable_on, measure.restrict_union hst hs ht, integral_add_measure hfs hft]

lemma integral_union_ae (hst : (s ∩ t : set α) =ᵐ[μ] (∅ : set α)) (hs : measurable_set s)
  (ht : measurable_set t) (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
begin
  have : s =ᵐ[μ] s \ t,
  { refine (hst.mem_iff.mono _).set_eq, simp },
  rw [← diff_union_self, integral_union disjoint_diff.symm, set_integral_congr_set_ae this],
  exacts [hs.diff ht, ht, hfs.mono_set (diff_subset _ _), hft]
end

lemma integral_diff (hs : measurable_set s) (ht : measurable_set t) (hfs : integrable_on f s μ)
  (hft : integrable_on f t μ) (hts : t ⊆ s) :
  ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ :=
begin
  rw [eq_sub_iff_add_eq, ← integral_union, diff_union_of_subset hts],
  exacts [disjoint_diff.symm, hs.diff ht, ht, hfs.mono_set (diff_subset _ _), hft]
end

lemma integral_finset_bUnion {ι : Type*} (t : finset ι) {s : ι → set α}
  (hs : ∀ i ∈ t, measurable_set (s i)) (h's : pairwise_on ↑t (disjoint on s))
  (hf : ∀ i ∈ t, integrable_on f (s i) μ) :
  ∫ x in (⋃ i ∈ t, s i), f x ∂ μ = ∑ i in t, ∫ x in s i, f x ∂ μ :=
begin
  induction t using finset.induction_on with a t hat IH hs h's,
  { simp },
  { simp only [finset.coe_insert, finset.forall_mem_insert, set.pairwise_on_insert,
      finset.set_bUnion_insert] at hs hf h's ⊢,
    rw [integral_union _ hs.1 _ hf.1 (integrable_on_finset_Union.2 hf.2)],
    { rw [finset.sum_insert hat, IH hs.2 h's.1 hf.2] },
    { simp only [disjoint_Union_right],
      exact (λ i hi, (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1) },
    { exact finset.measurable_set_bUnion _ hs.2 } }
end

lemma integral_fintype_Union {ι : Type*} [fintype ι] {s : ι → set α}
  (hs : ∀ i, measurable_set (s i)) (h's : pairwise (disjoint on s))
  (hf : ∀ i, integrable_on f (s i) μ) :
  ∫ x in (⋃ i, s i), f x ∂ μ = ∑ i, ∫ x in s i, f x ∂ μ :=
begin
  convert integral_finset_bUnion finset.univ (λ i hi, hs i) _ (λ i _, hf i),
  { simp },
  { simp [pairwise_on_univ, h's] }
end

lemma integral_empty : ∫ x in ∅, f x ∂μ = 0 := by rw [measure.restrict_empty, integral_zero_measure]

lemma integral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [measure.restrict_univ]

lemma integral_add_compl (hs : measurable_set s) (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_union (@disjoint_compl_right (set α) _ _) hs hs.compl
    hfi.integrable_on hfi.integrable_on, union_compl_self, integral_univ]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
lemma integral_indicator (hs : measurable_set s) :
  ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  by_cases hf : ae_measurable f (μ.restrict s), swap,
  { rw integral_non_ae_measurable hf,
    rw [← ae_measurable_indicator_iff hs] at hf,
    exact integral_non_ae_measurable hf },
  by_cases hfi : integrable_on f s μ, swap,
  { rwa [integral_undef, integral_undef],
    rwa integrable_indicator_iff hs },
  calc ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :
    (integral_add_compl hs (hfi.indicator hs)).symm
  ... = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :
    congr_arg2 (+) (integral_congr_ae (indicator_ae_eq_restrict hs))
      (integral_congr_ae (indicator_ae_eq_restrict_compl hs))
  ... = ∫ x in s, f x ∂μ : by simp
end

lemma tendsto_set_integral_of_monotone {ι : Type*} [encodable ι] [semilattice_sup ι]
  {s : ι → set α} {f : α → E} (hsm : ∀ i, measurable_set (s i))
  (h_mono : monotone s) (hfi : integrable_on f (⋃ n, s n) μ) :
  tendsto (λ i, ∫ a in s i, f a ∂μ) at_top (𝓝 (∫ a in (⋃ n, s n), f a ∂μ)) :=
begin
  have hfi' : ∫⁻ x in ⋃ n, s n, ∥f x∥₊ ∂μ < ∞ := hfi.2,
  set S := ⋃ i, s i,
  have hSm : measurable_set S := measurable_set.Union hsm,
  have hsub : ∀ {i}, s i ⊆ S, from subset_Union s,
  rw [← with_density_apply _ hSm] at hfi',
  set ν := μ.with_density (λ x, ∥f x∥₊) with hν,
  refine metric.nhds_basis_closed_ball.tendsto_right_iff.2 (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.le,
  have : ∀ᶠ i in at_top, ν (s i) ∈ Icc (ν S - ε) (ν S + ε),
    from tendsto_measure_Union hsm h_mono (ennreal.Icc_mem_nhds hfi'.ne (ennreal.coe_pos.2 ε0).ne'),
  refine this.mono (λ i hi, _),
  rw [mem_closed_ball_iff_norm', ← integral_diff hSm (hsm i) hfi (hfi.mono_set hsub) hsub,
    ← coe_nnnorm, nnreal.coe_le_coe, ← ennreal.coe_le_coe],
  refine (ennnorm_integral_le_lintegral_ennnorm _).trans _,
  rw [← with_density_apply _ (hSm.diff (hsm _)), ← hν, measure_diff hsub hSm (hsm _)],
  exacts [ennreal.sub_le_of_sub_le hi.1,
    (hi.2.trans_lt $ ennreal.add_lt_top.2 ⟨hfi', ennreal.coe_lt_top⟩).ne]
end

lemma has_sum_integral_Union {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  has_sum (λ n, ∫ a in s n, f a ∂ μ) (∫ a in ⋃ n, s n, f a ∂μ) :=
begin
  have hfi' : ∀ i, integrable_on f (s i) μ, from λ i, hfi.mono_set (subset_Union _ _),
  simp only [has_sum, ← integral_finset_bUnion _ (λ i _, hm i) (hd.pairwise_on _) (λ i _, hfi' i)],
  rw Union_eq_Union_finset at hfi ⊢,
  exact tendsto_set_integral_of_monotone (λ t, t.measurable_set_bUnion (λ i _, hm i))
    (λ t₁ t₂ h, bUnion_subset_bUnion_left h) hfi
end

lemma integral_Union {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  (∫ a in (⋃ n, s n), f a ∂μ) = ∑' n, ∫ a in s n, f a ∂ μ :=
(has_sum.tsum_eq (has_sum_integral_Union hm hd hfi)).symm

lemma set_integral_eq_zero_of_forall_eq_zero {f : α → E} (hf : measurable f)
  (ht_eq : ∀ x ∈ t, f x = 0) :
  ∫ x in t, f x ∂μ = 0 :=
begin
  refine integral_eq_zero_of_ae _,
  rw [eventually_eq, ae_restrict_iff (measurable_set_eq_fun hf measurable_zero)],
  refine eventually_of_forall (λ x hx, _),
  rw pi.zero_apply,
  exact ht_eq x hx,
end

private lemma set_integral_union_eq_left_of_disjoint {f : α → E} (hf : measurable f)
  (hfi : integrable f μ) (hs : measurable_set s) (ht : measurable_set t) (ht_eq : ∀ x ∈ t, f x = 0)
  (hs_disj : disjoint s t) :
  ∫ x in (s ∪ t), f x ∂μ = ∫ x in s, f x ∂μ :=
by rw [integral_union hs_disj hs ht hfi.integrable_on hfi.integrable_on,
  set_integral_eq_zero_of_forall_eq_zero hf ht_eq, add_zero]

lemma set_integral_union_eq_left {f : α → E} (hf : measurable f) (hfi : integrable f μ)
  (hs : measurable_set s) (ht : measurable_set t) (ht_eq : ∀ x ∈ t, f x = 0) :
  ∫ x in (s ∪ t), f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  let s_ := s \ {x | f x = 0},
  have hs_ : measurable_set s_, from hs.diff (measurable_set_eq_fun hf measurable_const),
  let s0 := s ∩ {x | f x = 0},
  have hs0 : measurable_set s0, from hs.inter (measurable_set_eq_fun hf measurable_const),
  have hs0_eq : ∀ x ∈ s0, f x = 0,
    by { intros x hx, simp_rw [s0, set.mem_inter_iff] at hx, exact hx.2, },
  have h_s_union : s = s_ ∪ s0, from (set.diff_union_inter s _).symm,
  have h_s_disj : disjoint s_ s0,
    from (@disjoint_sdiff_self_left (set α) {x | f x = 0} s _).mono_right
      (set.inter_subset_right _ _),
  rw [h_s_union, set_integral_union_eq_left_of_disjoint hf hfi hs_ hs0 hs0_eq h_s_disj],
  have hst0_eq : ∀ x ∈ s0 ∪ t, f x = 0,
  { intros x hx,
    rw set.mem_union at hx,
    cases hx,
    { exact hs0_eq x hx, },
    { exact ht_eq x hx, }, },
  have hst_disj : disjoint s_ (s0 ∪ t),
  { rw [← set.sup_eq_union, disjoint_sup_right],
    exact ⟨h_s_disj, (@disjoint_sdiff_self_left (set α) {x | f x = 0} s _).mono_right ht_eq⟩, },
  rw set.union_assoc,
  exact set_integral_union_eq_left_of_disjoint hf hfi hs_ (hs0.union ht) hst0_eq hst_disj,
end

lemma set_integral_neg_eq_set_integral_nonpos [linear_order E] [order_closed_topology E]
  {f : α → E} (hf : measurable f) (hfi : integrable f μ) :
  ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ :=
begin
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0},
    by { ext, simp_rw [set.mem_union_eq, set.mem_set_of_eq], exact le_iff_lt_or_eq, },
  rw h_union,
  exact (set_integral_union_eq_left hf hfi (measurable_set_lt hf measurable_const)
    (measurable_set_eq_fun hf measurable_const) (λ x hx, hx)).symm,
end

lemma integral_norm_eq_pos_sub_neg {f : α → ℝ} (hf : measurable f) (hfi : integrable f μ) :
  ∫ x, ∥f x∥ ∂μ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ :=
have h_meas : measurable_set {x | 0 ≤ f x}, from measurable_set_le measurable_const hf,
calc ∫ x, ∥f x∥ ∂μ = ∫ x in {x | 0 ≤ f x}, ∥f x∥ ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ∥f x∥ ∂μ :
  by rw ← integral_add_compl h_meas hfi.norm
... = ∫ x in {x | 0 ≤ f x}, f x ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ∥f x∥ ∂μ :
begin
  congr' 1,
  refine set_integral_congr h_meas (λ x hx, _),
  dsimp only,
  rw [real.norm_eq_abs, abs_eq_self.mpr _],
  exact hx,
end
... = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ :
begin
  congr' 1,
  rw ← integral_neg,
  refine set_integral_congr h_meas.compl (λ x hx, _),
  dsimp only,
  rw [real.norm_eq_abs, abs_eq_neg_self.mpr _],
  rw [set.mem_compl_iff, set.nmem_set_of_eq] at hx,
  linarith,
end
... = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ :
by { rw ← set_integral_neg_eq_set_integral_nonpos hf hfi, congr, ext1 x, simp, }

lemma set_integral_const (c : E) : ∫ x in s, c ∂μ = (μ s).to_real • c :=
by rw [integral_const, measure.restrict_apply_univ]

@[simp]
lemma integral_indicator_const (e : E) ⦃s : set α⦄ (s_meas : measurable_set s) :
  ∫ (a : α), s.indicator (λ (x : α), e) a ∂μ = (μ s).to_real • e :=
by rw [integral_indicator s_meas, ← set_integral_const]

lemma set_integral_indicator_const_Lp {p : ℝ≥0∞} (hs : measurable_set s) (ht : measurable_set t)
  (hμt : μ t ≠ ∞) (x : E) :
  ∫ a in s, indicator_const_Lp p ht hμt x a ∂μ = (μ (t ∩ s)).to_real • x :=
calc ∫ a in s, indicator_const_Lp p ht hμt x a ∂μ
    = (∫ a in s, t.indicator (λ _, x) a ∂μ) :
  by rw set_integral_congr_ae hs (indicator_const_Lp_coe_fn.mono (λ x hx hxs, hx))
... = (μ (t ∩ s)).to_real • x : by rw [integral_indicator_const _ ht, measure.restrict_apply ht]

lemma integral_indicator_const_Lp {p : ℝ≥0∞} (ht : measurable_set t) (hμt : μ t ≠ ∞) (x : E) :
  ∫ a, indicator_const_Lp p ht hμt x a ∂μ = (μ t).to_real • x :=
calc ∫ a, indicator_const_Lp p ht hμt x a ∂μ
    = ∫ a in univ, indicator_const_Lp p ht hμt x a ∂μ : by rw integral_univ
... = (μ (t ∩ univ)).to_real • x : set_integral_indicator_const_Lp measurable_set.univ ht hμt x
... = (μ t).to_real • x : by rw inter_univ

lemma set_integral_map {β} [measurable_space β] {g : α → β} {f : β → E} {s : set β}
  (hs : measurable_set s) (hf : ae_measurable f (measure.map g μ)) (hg : measurable g) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
begin
  rw [measure.restrict_map hg hs, integral_map hg (hf.mono_measure _)],
  exact measure.map_mono g measure.restrict_le_self
end

lemma set_integral_map_of_closed_embedding [topological_space α] [borel_space α]
  {β} [measurable_space β] [topological_space β] [borel_space β]
  {g : α → β} {f : β → E} {s : set β} (hs : measurable_set s) (hg : closed_embedding g) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
begin
  rw [measure.restrict_map hg.measurable hs, integral_map_of_closed_embedding hg],
  apply_instance,
end

lemma set_integral_map_equiv {β} [measurable_space β] (e : α ≃ᵐ β) (f : β → E) (s : set β) :
  ∫ y in s, f y ∂(measure.map e μ) = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
by rw [e.restrict_map, integral_map_equiv]

lemma norm_set_integral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  rw ← measure.restrict_apply_univ at *,
  haveI : is_finite_measure (μ.restrict s) := ⟨‹_›⟩,
  exact norm_integral_le_of_norm_le_const hC
end

lemma norm_set_integral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) (hfm : ae_measurable f (μ.restrict s)) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  apply norm_set_integral_le_of_norm_le_const_ae hs,
  have A : ∀ᵐ (x : α) ∂μ, x ∈ s → ∥ae_measurable.mk f hfm x∥ ≤ C,
  { filter_upwards [hC, hfm.ae_mem_imp_eq_mk],
    assume a h1 h2 h3,
    rw [← h2 h3],
    exact h1 h3 },
  have B : measurable_set {x | ∥(hfm.mk f) x∥ ≤ C} := hfm.measurable_mk.norm measurable_set_Iic,
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A],
  assume a h1 h2,
  rwa h1
end

lemma norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : measurable_set s)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae hs $ by rwa [ae_restrict_eq hsm, eventually_inf_principal]

lemma norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ x ∈ s, ∥f x∥ ≤ C) (hfm : ae_measurable f (μ.restrict s)) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae' hs (eventually_of_forall hC) hfm

lemma norm_set_integral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : measurable_set s)
  (hC : ∀ x ∈ s, ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae'' hs hsm $ eventually_of_forall hC

lemma set_integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
  (hfi : integrable_on f s μ) :
  ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
integral_eq_zero_iff_of_nonneg_ae hf hfi

lemma set_integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
  (hfi : integrable_on f s μ) :
  0 < ∫ x in s, f x ∂μ ↔ 0 < μ (support f ∩ s) :=
begin
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, restrict_apply_of_null_measurable_set],
  exact hfi.ae_measurable.null_measurable_set (measurable_set_singleton 0).compl
end

lemma set_integral_trim {α} {m m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0) {f : α → E}
  (hf_meas : @measurable _ _ m _ f) {s : set α} (hs : measurable_set[m] s) :
  ∫ x in s, f x ∂μ = ∫ x in s, f x ∂(μ.trim hm) :=
by rwa [integral_trim hm hf_meas, restrict_trim hm μ]

end normed_group

section mono

variables {μ : measure α} {f g : α → ℝ} {s t : set α}
  (hf : integrable_on f s μ) (hg : integrable_on g s μ)

lemma set_integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
integral_mono_ae hf hg h

lemma set_integral_mono_ae (h : f ≤ᵐ[μ] g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
set_integral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

lemma set_integral_mono_on (hs : measurable_set s) (h : ∀ x ∈ s, f x ≤ g x) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
set_integral_mono_ae_restrict hf hg
  (by simp [hs, eventually_le, eventually_inf_principal, ae_of_all _ h])

include hf hg  -- why do I need this include, but we don't need it in other lemmas?
lemma set_integral_mono_on_ae (hs : measurable_set s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
by { refine set_integral_mono_ae_restrict hf hg _, rwa [eventually_le, ae_restrict_iff' hs], }
omit hf hg

lemma set_integral_mono (h : f ≤ g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
integral_mono hf hg h

lemma set_integral_mono_set (hfi : integrable f μ) (hf : 0 ≤ᵐ[μ] f) (hst : s ≤ᵐ[μ] t) :
  ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
begin
  repeat { rw integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf)
            (hfi.1.mono_measure measure.restrict_le_self) },
  rw ennreal.to_real_le_to_real
    (ne_of_lt $ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2)
    (ne_of_lt $ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2),
  exact (lintegral_mono_set' hst),
end

end mono

section nonneg

variables {μ : measure α} {f : α → ℝ} {s : set α}

lemma set_integral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) :
  0 ≤ ∫ a in s, f a ∂μ :=
integral_nonneg_of_ae hf

lemma set_integral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a in s, f a ∂μ :=
set_integral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

lemma set_integral_nonneg (hs : measurable_set s) (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  0 ≤ ∫ a in s, f a ∂μ :=
set_integral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

lemma set_integral_nonneg_ae (hs : measurable_set s) (hf : ∀ᵐ a ∂μ, a ∈ s → 0 ≤ f a) :
  0 ≤ ∫ a in s, f a ∂μ :=
set_integral_nonneg_of_ae_restrict $ by rwa [eventually_le, ae_restrict_iff' hs]

lemma set_integral_le_nonneg {s : set α} (hs : measurable_set s) (hf : measurable f)
  (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ :=
begin
  rw [← integral_indicator hs, ← integral_indicator (measurable_set_le measurable_const hf)],
  exact integral_mono (hfi.indicator hs) (hfi.indicator (measurable_set_le measurable_const hf))
    (indicator_le_indicator_nonneg s f),
end

lemma set_integral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) :
  ∫ a in s, f a ∂μ ≤ 0 :=
integral_nonpos_of_ae hf

lemma set_integral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : ∫ a in s, f a ∂μ ≤ 0 :=
set_integral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

lemma set_integral_nonpos (hs : measurable_set s) (hf : ∀ a, a ∈ s → f a ≤ 0) :
  ∫ a in s, f a ∂μ ≤ 0 :=
set_integral_nonpos_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

lemma set_integral_nonpos_ae (hs : measurable_set s) (hf : ∀ᵐ a ∂μ, a ∈ s → f a ≤ 0) :
  ∫ a in s, f a ∂μ ≤ 0 :=
set_integral_nonpos_of_ae_restrict $ by rwa [eventually_le, ae_restrict_iff' hs]

lemma set_integral_nonpos_le {s : set α} (hs : measurable_set s) {f : α → ℝ} (hf : measurable f)
  (hfi : integrable f μ) :
  ∫ x in {y | f y ≤ 0}, f x ∂μ ≤ ∫ x in s, f x ∂μ :=
begin
  rw [← integral_indicator hs, ← integral_indicator (measurable_set_le hf measurable_const)],
  exact integral_mono (hfi.indicator (measurable_set_le hf measurable_const)) (hfi.indicator hs)
    (indicator_nonpos_le_indicator s f),
end

end nonneg

section tendsto_mono

variables {μ : measure α}
  [measurable_space E] [normed_group E] [borel_space E] [complete_space E] [normed_space ℝ E]
  [second_countable_topology E] {s : ℕ → set α} {f : α → E}

lemma tendsto_set_integral_of_antitone (hsm : ∀ i, measurable_set (s i))
  (h_mono : ∀ i j, i ≤ j → s j ⊆ s i) (hfi : integrable_on f (s 0) μ) :
  tendsto (λi, ∫ a in s i, f a ∂μ) at_top (𝓝 (∫ a in (⋂ n, s n), f a ∂μ)) :=
begin
  let bound : α → ℝ := indicator (s 0) (λ a, ∥f a∥),
  have h_int_eq : (λ i, ∫ a in s i, f a ∂μ) = (λ i, ∫ a, (s i).indicator f a ∂μ),
    from funext (λ i, (integral_indicator (hsm i)).symm),
  rw h_int_eq,
  rw ← integral_indicator (measurable_set.Inter hsm),
  refine tendsto_integral_of_dominated_convergence bound _ _ _ _ _,
  { intro n,
    rw ae_measurable_indicator_iff (hsm n),
    exact (integrable_on.mono_set hfi (h_mono 0 n (zero_le n))).1, },
  { rw ae_measurable_indicator_iff (measurable_set.Inter hsm),
    exact (integrable_on.mono_set hfi (set.Inter_subset s 0)).1, },
  { rw integrable_indicator_iff (hsm 0),
    exact hfi.norm, },
  { simp_rw norm_indicator_eq_indicator_norm,
    refine λ n, eventually_of_forall (λ x, _),
    exact indicator_le_indicator_of_subset (h_mono 0 n (zero_le n)) (λ a, norm_nonneg _) _, },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_antitone _ h_mono _ _) (pure_le_nhds _), },
end

end tendsto_mono

section continuous_set_integral
/-! ### Continuity of the set integral

We prove that for any set `s`, the function `λ f : α →₁[μ] E, ∫ x in s, f x ∂μ` is continuous. -/

variables [normed_group E] [measurable_space E] [second_countable_topology E] [borel_space E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space 𝕜]
  [normed_group F] [measurable_space F] [second_countable_topology F] [borel_space F]
  [normed_space 𝕜 F]
  {p : ℝ≥0∞} {μ : measure α}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is additive. -/
lemma Lp_to_Lp_restrict_add (f g : Lp E p μ) (s : set α) :
  ((Lp.mem_ℒp (f + g)).restrict s).to_Lp ⇑(f + g)
    = ((Lp.mem_ℒp f).restrict s).to_Lp f + ((Lp.mem_ℒp g).restrict s).to_Lp g :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _,
  refine (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))
    (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono (λ x hx1 hx2 hx3 hx4 hx5, _),
  rw [hx4, hx1, pi.add_apply, hx2, hx3, hx5, pi.add_apply],
end

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map commutes with scalar multiplication. -/
lemma Lp_to_Lp_restrict_smul [opens_measurable_space 𝕜] (c : 𝕜) (f : Lp F p μ) (s : set α) :
  ((Lp.mem_ℒp (c • f)).restrict s).to_Lp ⇑(c • f) = c • (((Lp.mem_ℒp f).restrict s).to_Lp f) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _,
  refine (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono
    (λ x hx1 hx2 hx3 hx4, _),
  rw [hx2, hx1, pi.smul_apply, hx3, hx4, pi.smul_apply],
end

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is non-expansive. -/
lemma norm_Lp_to_Lp_restrict_le (s : set α) (f : Lp E p μ) :
  ∥((Lp.mem_ℒp f).restrict s).to_Lp f∥ ≤ ∥f∥ :=
begin
  rw [Lp.norm_def, Lp.norm_def, ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)],
  refine (le_of_eq _).trans (snorm_mono_measure _ measure.restrict_le_self),
  { exact s, },
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _),
end

variables (α F 𝕜)
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_clm [borel_space 𝕜] (μ : measure α) (p : ℝ≥0∞) [hp : fact (1 ≤ p)]
  (s : set α) :
  Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
@linear_map.mk_continuous 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _
  ⟨λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s), λ f g, Lp_to_Lp_restrict_add f g s,
    λ c f, Lp_to_Lp_restrict_smul c f s⟩
  1 (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le s f, })

variables {α F 𝕜}

variables (𝕜)
lemma Lp_to_Lp_restrict_clm_coe_fn [borel_space 𝕜] [hp : fact (1 ≤ p)] (s : set α) (f : Lp F p μ) :
  Lp_to_Lp_restrict_clm α F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)
variables {𝕜}

@[continuity]
lemma continuous_set_integral [normed_space ℝ E] [complete_space E] (s : set α) :
  continuous (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ) :=
begin
  haveI : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
  have h_comp : (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ)
    = (integral (μ.restrict s)) ∘ (λ f, Lp_to_Lp_restrict_clm α E ℝ μ 1 s f),
  { ext1 f,
    rw [function.comp_apply, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)], },
  rw h_comp,
  exact continuous_integral.comp (Lp_to_Lp_restrict_clm α E ℝ μ 1 s).continuous,
end

end continuous_set_integral


end measure_theory

open measure_theory asymptotics metric

variables {ι : Type*} [measurable_space E] [normed_group E]

/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.lift'
powerset` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma filter.tendsto.integral_sub_linear_is_o_ae
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} {l : filter α} [l.is_measurably_generated]
  {f : α → E} {b : E} (h : tendsto f (l ⊓ μ.ae) (𝓝 b))
  (hfm : measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li (l.lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • b) m li :=
begin
  suffices : is_o (λ s, ∫ x in s, f x ∂μ - (μ s).to_real • b) (λ s, (μ s).to_real)
    (l.lift' powerset),
    from (this.comp_tendsto hs).congr' (hsμ.mono $ λ a ha, ha ▸ rfl) hsμ,
  refine is_o_iff.2 (λ ε ε₀, _),
  have : ∀ᶠ s in l.lift' powerset, ∀ᶠ x in μ.ae, x ∈ s → f x ∈ closed_ball b ε :=
    eventually_lift'_powerset_eventually.2 (h.eventually $ closed_ball_mem_nhds _ ε₀),
  filter_upwards [hμ.eventually, (hμ.integrable_at_filter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this],
  simp only [mem_closed_ball, dist_eq_norm],
  intros s hμs h_integrable hfm h_norm,
  rw [← set_integral_const, ← integral_sub h_integrable (integrable_on_const.2 $ or.inr hμs),
    real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
  exact norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub ae_measurable_const)
end

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).lift' powerset` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_within_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (ha : continuous_within_at f t a) (ht : measurable_set t)
  (hfm : measurable_at_filter f (𝓝[t] a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝[t] a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
by haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _;
exact (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae
  hfm (μ.finite_at_nhds_within a t) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to `(𝓝 a).lift'
powerset` along `li.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α}
  {f : α → E} (ha : continuous_at f a) (hfm : measurable_at_filter f (𝓝 a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝 a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds a) hs m hsμ

/-- If a function is continuous on an open set `s`, then it is measurable at the filter `𝓝 x` for
  all `x ∈ s`. -/
lemma continuous_on.measurable_at_filter
  [topological_space α] [opens_measurable_space α] [borel_space E]
  {f : α → E} {s : set α} {μ : measure α} (hs : is_open s) (hf : continuous_on f s) :
  ∀ x ∈ s, measurable_at_filter f (𝓝 x) μ :=
λ x hx, ⟨s, is_open.mem_nhds hs hx, hf.ae_measurable hs.measurable_set⟩

lemma continuous_at.measurable_at_filter
  [topological_space α] [opens_measurable_space α] [borel_space E]
  {f : α → E} {s : set α} {μ : measure α} (hs : is_open s) (hf : ∀ x ∈ s, continuous_at f x) :
  ∀ x ∈ s, measurable_at_filter f (𝓝 x) μ :=
continuous_on.measurable_at_filter hs $ continuous_at.continuous_on hf

/-- If a function is continuous on a measurable set `s`, then it is measurable at the filter
  `𝓝[s] x` for all `x`. -/
lemma continuous_on.measurable_at_filter_nhds_within {α E : Type*} [measurable_space α]
  [measurable_space E] [normed_group E] [topological_space α] [opens_measurable_space α]
  [borel_space E] {f : α → E} {s : set α} {μ : measure α}
  (hf : continuous_on f s) (hs : measurable_set s) (x : α) :
  measurable_at_filter f (𝓝[s] x) μ :=
⟨s, self_mem_nhds_within, hf.ae_measurable hs⟩

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).lift' powerset` along
`li`.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_on.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (hft : continuous_on f t) (ha : a ∈ t) (ht : measurable_set t)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝[t] a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(hft a ha).integral_sub_linear_is_o_ae ht ⟨t, self_mem_nhds_within, hft.ae_measurable ht⟩ hs m hsμ

section
/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `continuous_linear_map.comp_Lp`. We take advantage of this construction here.
-/

variables {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  [normed_group F] [normed_space 𝕜 F]
  {p : ennreal}

local attribute [instance] fact_one_le_one_ennreal

namespace continuous_linear_map

variables [measurable_space F] [borel_space F]

variables [second_countable_topology F] [complete_space F]
  [borel_space E] [second_countable_topology E] [normed_space ℝ F]

lemma integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) :
  ∫ a, (L.comp_Lp φ) a ∂μ = ∫ a, L (φ a) ∂μ :=
integral_congr_ae $ coe_fn_comp_Lp _ _

lemma set_integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) {s : set α} (hs : measurable_set s) :
  ∫ a in s, (L.comp_Lp φ) a ∂μ = ∫ a in s, L (φ a) ∂μ :=
set_integral_congr_ae hs ((L.coe_fn_comp_Lp φ).mono (λ x hx hx2, hx))

lemma continuous_integral_comp_L1 [measurable_space 𝕜] [opens_measurable_space 𝕜] (L : E →L[𝕜] F) :
  continuous (λ (φ : α →₁[μ] E), ∫ (a : α), L (φ a) ∂μ) :=
by { rw ← funext L.integral_comp_Lp, exact continuous_integral.comp (L.comp_LpL 1 μ).continuous, }

variables [complete_space E] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E] [is_scalar_tower ℝ 𝕜 F]

lemma integral_comp_comm (L : E →L[𝕜] F) {φ : α → E} (φ_int : integrable φ μ) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
begin
  apply integrable.induction (λ φ, ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ)),
  { intros e s s_meas s_finite,
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ s).to_real e,
      continuous_linear_map.map_smul, @smul_one_smul F ℝ 𝕜 _ _ _ _ _ (μ s).to_real (L e),
      ← integral_indicator_const (L e) s_meas],
    congr' 1 with a,
    rw set.indicator_comp_of_zero L.map_zero },
  { intros f g H f_int g_int hf hg,
    simp [L.map_add, integral_add f_int g_int,
      integral_add (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg] },
  { exact is_closed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral) },
  { intros f g hfg f_int hf,
    convert hf using 1 ; clear hf,
    { exact integral_congr_ae (hfg.fun_comp L).symm },
    { rw integral_congr_ae hfg.symm } },
  all_goals { assumption }
end

lemma integral_apply {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E] {φ : α → H →L[ℝ] E} (φ_int : integrable φ μ) (v : H) :
  (∫ a, φ a ∂μ) v = ∫ a, φ a v ∂μ :=
((continuous_linear_map.apply ℝ E v).integral_comp_comm φ_int).symm

lemma integral_comp_comm' (L : E →L[𝕜] F) {K} (hL : antilipschitz_with K L) (φ : α → E) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
begin
  by_cases h : integrable φ μ,
  { exact integral_comp_comm L h },
  have : ¬ (integrable (L ∘ φ) μ),
    by rwa lipschitz_with.integrable_comp_iff_of_antilipschitz L.lipschitz hL (L.map_zero),
  simp [integral_undef, h, this]
end

lemma integral_comp_L1_comm (L : E →L[𝕜] F) (φ : α →₁[μ] E) : ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.integral_comp_comm (L1.integrable_coe_fn φ)

end continuous_linear_map

namespace linear_isometry

variables [measurable_space F] [borel_space F] [second_countable_topology F] [complete_space F]
  [normed_space ℝ F] [is_scalar_tower ℝ 𝕜 F]
  [borel_space E] [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [is_scalar_tower ℝ 𝕜 E]
  [measurable_space 𝕜] [opens_measurable_space 𝕜]

lemma integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : α → E) : ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.to_continuous_linear_map.integral_comp_comm' L.antilipschitz _

end linear_isometry

variables [borel_space E] [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [measurable_space F] [borel_space F] [second_countable_topology F] [complete_space F]
  [normed_space ℝ F]
  [measurable_space 𝕜] [borel_space 𝕜]

@[norm_cast] lemma integral_of_real {f : α → ℝ} : ∫ a, (f a : 𝕜) ∂μ = ↑∫ a, f a ∂μ :=
(@is_R_or_C.of_real_li 𝕜 _).integral_comp_comm f

lemma integral_re {f : α → 𝕜} (hf : integrable f μ) :
  ∫ a, is_R_or_C.re (f a) ∂μ = is_R_or_C.re ∫ a, f a ∂μ :=
(@is_R_or_C.re_clm 𝕜 _).integral_comp_comm hf

lemma integral_im {f : α → 𝕜} (hf : integrable f μ) :
  ∫ a, is_R_or_C.im (f a) ∂μ = is_R_or_C.im ∫ a, f a ∂μ :=
(@is_R_or_C.im_clm 𝕜 _).integral_comp_comm hf

lemma integral_conj {f : α → 𝕜} : ∫ a, is_R_or_C.conj (f a) ∂μ = is_R_or_C.conj ∫ a, f a ∂μ :=
(@is_R_or_C.conj_lie 𝕜 _).to_linear_isometry.integral_comp_comm f

lemma fst_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ :=
((continuous_linear_map.fst ℝ E F).integral_comp_comm hf).symm

lemma snd_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ :=
((continuous_linear_map.snd ℝ E F).integral_comp_comm hf).symm

lemma integral_pair {f : α → E} {g : α → F} (hf : integrable f μ) (hg : integrable g μ) :
  ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
have _ := hf.prod_mk hg, prod.ext (fst_integral this) (snd_integral this)

lemma integral_smul_const (f : α → ℝ) (c : E) :
  ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c :=
begin
  by_cases hf : integrable f μ,
  { exact ((continuous_linear_map.id ℝ ℝ).smul_right c).integral_comp_comm hf },
  { by_cases hc : c = 0,
    { simp only [hc, integral_zero, smul_zero] },
    rw [integral_undef hf, integral_undef, zero_smul],
    simp_rw [integrable_smul_const hc, hf, not_false_iff] }
end

section inner

variables {E' : Type*} [inner_product_space 𝕜 E'] [measurable_space E'] [borel_space E']
  [second_countable_topology E'] [complete_space E'] [normed_space ℝ E'] [is_scalar_tower ℝ 𝕜 E']

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E' _ x y

lemma integral_inner {f : α → E'} (hf : integrable f μ) (c : E') :
  ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
((@inner_right 𝕜 E' _ _ c).restrict_scalars ℝ).integral_comp_comm hf

lemma integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E') (hf : integrable f μ)
  (hf_int : ∀ (c : E'), ∫ x, ⟪c, f x⟫ ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }

end inner

end
