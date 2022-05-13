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
as `s` tends to `l.small_sets`, i.e. for any `ε>0` there exists `t ∈ l` such that
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

variables [normed_group E]  {f g : α → E} {s t : set α} {μ ν : measure α}
  {l l' : filter α}

variables [complete_space E] [normed_space ℝ E]

lemma set_integral_congr_ae (hs : measurable_set s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
integral_congr_ae ((ae_restrict_iff' hs).2 h)

lemma set_integral_congr (hs : measurable_set s) (h : eq_on f g s) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
set_integral_congr_ae hs $ eventually_of_forall h

lemma set_integral_congr_set_ae (hst : s =ᵐ[μ] t) :
  ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ :=
by rw measure.restrict_congr_set hst

lemma integral_union_ae (hst : ae_disjoint μ s t) (ht : null_measurable_set t μ)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
by simp only [integrable_on, measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

lemma integral_union (hst : disjoint s t) (ht : measurable_set t)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
integral_union_ae hst.ae_disjoint ht.null_measurable_set hfs hft

lemma integral_diff (ht : measurable_set t) (hfs : integrable_on f s μ)
  (hft : integrable_on f t μ) (hts : t ⊆ s) :
  ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ :=
begin
  rw [eq_sub_iff_add_eq, ← integral_union, diff_union_of_subset hts],
  exacts [disjoint_diff.symm, ht, hfs.mono_set (diff_subset _ _), hft]
end

lemma integral_finset_bUnion {ι : Type*} (t : finset ι) {s : ι → set α}
  (hs : ∀ i ∈ t, measurable_set (s i)) (h's : set.pairwise ↑t (disjoint on s))
  (hf : ∀ i ∈ t, integrable_on f (s i) μ) :
  ∫ x in (⋃ i ∈ t, s i), f x ∂ μ = ∑ i in t, ∫ x in s i, f x ∂ μ :=
begin
  induction t using finset.induction_on with a t hat IH hs h's,
  { simp },
  { simp only [finset.coe_insert, finset.forall_mem_insert, set.pairwise_insert,
      finset.set_bUnion_insert] at hs hf h's ⊢,
    rw [integral_union _ _ hf.1 (integrable_on_finset_Union.2 hf.2)],
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
  { simp [pairwise_univ, h's] }
end

lemma integral_empty : ∫ x in ∅, f x ∂μ = 0 := by rw [measure.restrict_empty, integral_zero_measure]

lemma integral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [measure.restrict_univ]

lemma integral_add_compl (hs : measurable_set s) (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_union (@disjoint_compl_right (set α) _ _) hs.compl
    hfi.integrable_on hfi.integrable_on, union_compl_self, integral_univ]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
lemma integral_indicator (hs : measurable_set s) :
  ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ :=
begin
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

lemma of_real_set_integral_one_of_measure_ne_top {α : Type*} {m : measurable_space α}
  {μ : measure α} {s : set α} (hs : μ s ≠ ∞) :
  ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
calc
ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ)
    = ennreal.of_real (∫ x in s, ∥(1 : ℝ)∥ ∂μ) : by simp only [norm_one]
... = ∫⁻ x in s, 1 ∂μ :
begin
  rw of_real_integral_norm_eq_lintegral_nnnorm (integrable_on_const.2 (or.inr hs.lt_top)),
  simp only [nnnorm_one, ennreal.coe_one],
end
... = μ s : set_lintegral_one _

lemma of_real_set_integral_one {α : Type*} {m : measurable_space α} (μ : measure α)
  [is_finite_measure μ] (s : set α) :
  ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
of_real_set_integral_one_of_measure_ne_top (measure_ne_top μ s)

lemma integral_piecewise [decidable_pred (∈ s)] (hs : measurable_set s)
  {f g : α → E} (hf : integrable_on f s μ) (hg : integrable_on g sᶜ μ) :
  ∫ x, s.piecewise f g x ∂μ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, g x ∂μ :=
by rw [← set.indicator_add_compl_eq_piecewise,
  integral_add' (hf.indicator hs) (hg.indicator hs.compl),
  integral_indicator hs, integral_indicator hs.compl]

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
    from tendsto_measure_Union h_mono (ennreal.Icc_mem_nhds hfi'.ne (ennreal.coe_pos.2 ε0).ne'),
  refine this.mono (λ i hi, _),
  rw [mem_closed_ball_iff_norm', ← integral_diff (hsm i) hfi (hfi.mono_set hsub) hsub,
    ← coe_nnnorm, nnreal.coe_le_coe, ← ennreal.coe_le_coe],
  refine (ennnorm_integral_le_lintegral_ennnorm _).trans _,
  rw [← with_density_apply _ (hSm.diff (hsm _)), ← hν, measure_diff hsub (hsm _)],
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt $ ennreal.add_lt_top.2 ⟨hfi', ennreal.coe_lt_top⟩).ne]
end

lemma has_sum_integral_Union_ae {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, null_measurable_set (s i) μ) (hd : pairwise (ae_disjoint μ on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  has_sum (λ n, ∫ a in s n, f a ∂ μ) (∫ a in ⋃ n, s n, f a ∂μ) :=
begin
  simp only [integrable_on, measure.restrict_Union_ae hd hm] at hfi ⊢,
  exact has_sum_integral_measure hfi
end

lemma has_sum_integral_Union {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  has_sum (λ n, ∫ a in s n, f a ∂ μ) (∫ a in ⋃ n, s n, f a ∂μ) :=
has_sum_integral_Union_ae (λ i, (hm i).null_measurable_set) (hd.mono (λ i j h, h.ae_disjoint)) hfi

lemma integral_Union {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  (∫ a in (⋃ n, s n), f a ∂μ) = ∑' n, ∫ a in s n, f a ∂ μ :=
(has_sum.tsum_eq (has_sum_integral_Union hm hd hfi)).symm

lemma integral_Union_ae {ι : Type*} [encodable ι] {s : ι → set α} {f : α → E}
  (hm : ∀ i, null_measurable_set (s i) μ) (hd : pairwise (ae_disjoint μ on s))
  (hfi : integrable_on f (⋃ i, s i) μ) :
  (∫ a in (⋃ n, s n), f a ∂μ) = ∑' n, ∫ a in s n, f a ∂ μ :=
(has_sum.tsum_eq (has_sum_integral_Union_ae hm hd hfi)).symm

lemma set_integral_eq_zero_of_forall_eq_zero {f : α → E} (hf : strongly_measurable f)
  (ht_eq : ∀ x ∈ t, f x = 0) :
  ∫ x in t, f x ∂μ = 0 :=
begin
  refine integral_eq_zero_of_ae _,
  rw [eventually_eq, ae_restrict_iff (hf.measurable_set_eq_fun strongly_measurable_zero)],
  refine eventually_of_forall (λ x hx, _),
  rw pi.zero_apply,
  exact ht_eq x hx,
end

lemma set_integral_union_eq_left {f : α → E} (hf : strongly_measurable f) (hfi : integrable f μ)
  (hs : measurable_set s) (ht_eq : ∀ x ∈ t, f x = 0) :
  ∫ x in (s ∪ t), f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw [← set.union_diff_self, union_comm, integral_union,
    set_integral_eq_zero_of_forall_eq_zero _ (λ x hx, ht_eq x (diff_subset _ _ hx)), zero_add],
  exacts [hf, disjoint_diff.symm, hs, hfi.integrable_on, hfi.integrable_on]
end

lemma set_integral_neg_eq_set_integral_nonpos [linear_order E] [order_closed_topology E]
  {f : α → E} (hf : strongly_measurable f) (hfi : integrable f μ) :
  ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ :=
begin
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0},
    by { ext, simp_rw [set.mem_union_eq, set.mem_set_of_eq], exact le_iff_lt_or_eq, },
  rw h_union,
  exact (set_integral_union_eq_left hf hfi (hf.measurable_set_lt strongly_measurable_const)
    (λ x hx, hx)).symm,
end

lemma integral_norm_eq_pos_sub_neg {f : α → ℝ} (hf : strongly_measurable f)
  (hfi : integrable f μ) :
  ∫ x, ∥f x∥ ∂μ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ :=
have h_meas : measurable_set {x | 0 ≤ f x}, from strongly_measurable_const.measurable_set_le hf,
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

@[simp]
lemma integral_indicator_one ⦃s : set α⦄ (hs : measurable_set s) :
  ∫ a, s.indicator 1 a ∂μ = (μ s).to_real :=
(integral_indicator_const 1 hs).trans ((smul_eq_mul _).trans (mul_one _))

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
  (hs : measurable_set s)
  (hf : ae_strongly_measurable f (measure.map g μ)) (hg : ae_measurable g μ) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
begin
  rw [measure.restrict_map_of_ae_measurable hg hs,
      integral_map (hg.mono_measure measure.restrict_le_self) (hf.mono_measure _)],
  exact measure.map_mono_of_ae_measurable measure.restrict_le_self hg
end

lemma _root_.measurable_embedding.set_integral_map {β} {_ : measurable_space β} {f : α → β}
  (hf : measurable_embedding f) (g : β → E) (s : set β) :
  ∫ y in s, g y ∂(measure.map f μ) = ∫ x in f ⁻¹' s, g (f x) ∂μ :=
by rw [hf.restrict_map, hf.integral_map]

lemma _root_.closed_embedding.set_integral_map [topological_space α] [borel_space α]
  {β} [measurable_space β] [topological_space β] [borel_space β]
  {g : α → β} {f : β → E} (s : set β) (hg : closed_embedding g) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
hg.measurable_embedding.set_integral_map _ _

lemma measure_preserving.set_integral_preimage_emb {β} {_ : measurable_space β} {f : α → β} {ν}
  (h₁ : measure_preserving f μ ν) (h₂ : measurable_embedding f) (g : β → E) (s : set β) :
  ∫ x in f ⁻¹' s, g (f x) ∂μ = ∫ y in s, g y ∂ν :=
(h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

lemma measure_preserving.set_integral_image_emb {β} {_ : measurable_space β} {f : α → β} {ν}
  (h₁ : measure_preserving f μ ν) (h₂ : measurable_embedding f) (g : β → E) (s : set α) :
  ∫ y in f '' s, g y ∂ν = ∫ x in s, g (f x) ∂μ :=
eq.symm $ (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

lemma set_integral_map_equiv {β} [measurable_space β] (e : α ≃ᵐ β) (f : β → E) (s : set β) :
  ∫ y in s, f y ∂(measure.map e μ) = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
e.measurable_embedding.set_integral_map f s

lemma norm_set_integral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  rw ← measure.restrict_apply_univ at *,
  haveI : is_finite_measure (μ.restrict s) := ⟨‹_›⟩,
  exact norm_integral_le_of_norm_le_const hC
end

lemma norm_set_integral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) (hfm : ae_strongly_measurable f (μ.restrict s)) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  apply norm_set_integral_le_of_norm_le_const_ae hs,
  have A : ∀ᵐ (x : α) ∂μ, x ∈ s → ∥ae_strongly_measurable.mk f hfm x∥ ≤ C,
  { filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3,
    rw [← h2 h3],
    exact h1 h3 },
  have B : measurable_set {x | ∥(hfm.mk f) x∥ ≤ C} :=
    hfm.strongly_measurable_mk.norm.measurable measurable_set_Iic,
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _,
  rwa h1,
end

lemma norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : measurable_set s)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae hs $ by rwa [ae_restrict_eq hsm, eventually_inf_principal]

lemma norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ x ∈ s, ∥f x∥ ≤ C) (hfm : ae_strongly_measurable f (μ.restrict s)) :
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
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, measure.restrict_apply₀],
  rw support_eq_preimage,
  exact hfi.ae_strongly_measurable.ae_measurable.null_measurable (measurable_set_singleton 0).compl
end

lemma set_integral_trim {α} {m m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0) {f : α → E}
  (hf_meas : strongly_measurable[m] f) {s : set α} (hs : measurable_set[m] s) :
  ∫ x in s, f x ∂μ = ∫ x in s, f x ∂(μ.trim hm) :=
by rwa [integral_trim hm hf_meas, restrict_trim hm μ]

lemma integral_Icc_eq_integral_Ioc' [partial_order α] {f : α → E} {a b : α} (ha : μ {a} = 0) :
  ∫ t in Icc a b, f t ∂μ = ∫ t in Ioc a b, f t ∂μ :=
set_integral_congr_set_ae (Ioc_ae_eq_Icc' ha).symm

lemma integral_Ioc_eq_integral_Ioo' [partial_order α] {f : α → E} {a b : α} (hb : μ {b} = 0) :
  ∫ t in Ioc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
set_integral_congr_set_ae (Ioo_ae_eq_Ioc' hb).symm

lemma integral_Icc_eq_integral_Ioc [partial_order α] {f : α → E} {a b : α} [has_no_atoms μ] :
  ∫ t in Icc a b, f t ∂μ = ∫ t in Ioc a b, f t ∂μ :=
integral_Icc_eq_integral_Ioc' $ measure_singleton a

lemma integral_Ioc_eq_integral_Ioo [partial_order α] {f : α → E} {a b : α} [has_no_atoms μ] :
  ∫ t in Ioc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
integral_Ioc_eq_integral_Ioo' $ measure_singleton b

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

lemma set_integral_mono_set (hfi : integrable_on f t μ) (hf : 0 ≤ᵐ[μ.restrict t] f)
  (hst : s ≤ᵐ[μ] t) :
  ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
integral_mono_measure (measure.restrict_mono_ae hst) hf hfi

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

lemma set_integral_le_nonneg {s : set α} (hs : measurable_set s) (hf : strongly_measurable f)
  (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ :=
begin
  rw [← integral_indicator hs,
      ← integral_indicator (strongly_measurable_const.measurable_set_le hf)],
  exact integral_mono (hfi.indicator hs)
    (hfi.indicator (strongly_measurable_const.measurable_set_le hf))
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

lemma set_integral_nonpos_le {s : set α} (hs : measurable_set s) (hf : strongly_measurable f)
  (hfi : integrable f μ) :
  ∫ x in {y | f y ≤ 0}, f x ∂μ ≤ ∫ x in s, f x ∂μ :=
begin
  rw [← integral_indicator hs,
      ← integral_indicator (hf.measurable_set_le strongly_measurable_const)],
  exact integral_mono (hfi.indicator (hf.measurable_set_le strongly_measurable_const))
    (hfi.indicator hs) (indicator_nonpos_le_indicator s f),
end

end nonneg

section tendsto_mono

variables {μ : measure α} [normed_group E] [complete_space E] [normed_space ℝ E]
  {s : ℕ → set α} {f : α → E}

lemma _root_.antitone.tendsto_set_integral (hsm : ∀ i, measurable_set (s i))
  (h_anti : antitone s) (hfi : integrable_on f (s 0) μ) :
  tendsto (λi, ∫ a in s i, f a ∂μ) at_top (𝓝 (∫ a in (⋂ n, s n), f a ∂μ)) :=
begin
  let bound : α → ℝ := indicator (s 0) (λ a, ∥f a∥),
  have h_int_eq : (λ i, ∫ a in s i, f a ∂μ) = (λ i, ∫ a, (s i).indicator f a ∂μ),
    from funext (λ i, (integral_indicator (hsm i)).symm),
  rw h_int_eq,
  rw ← integral_indicator (measurable_set.Inter hsm),
  refine tendsto_integral_of_dominated_convergence bound _ _ _ _,
  { intro n,
    rw ae_strongly_measurable_indicator_iff (hsm n),
    exact (integrable_on.mono_set hfi (h_anti (zero_le n))).1 },
  { rw integrable_indicator_iff (hsm 0),
    exact hfi.norm, },
  { simp_rw norm_indicator_eq_indicator_norm,
    refine λ n, eventually_of_forall (λ x, _),
    exact indicator_le_indicator_of_subset (h_anti (zero_le n)) (λ a, norm_nonneg _) _ },
  { filter_upwards with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _), },
end

end tendsto_mono

/-! ### Continuity of the set integral

We prove that for any set `s`, the function `λ f : α →₁[μ] E, ∫ x in s, f x ∂μ` is continuous. -/

section continuous_set_integral
variables [normed_group E] {𝕜 : Type*} [is_R_or_C 𝕜] [normed_group F] [normed_space 𝕜 F]
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
lemma Lp_to_Lp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : set α) :
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
def Lp_to_Lp_restrict_clm (μ : measure α) (p : ℝ≥0∞) [hp : fact (1 ≤ p)] (s : set α) :
  Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
@linear_map.mk_continuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (ring_hom.id 𝕜)
  ⟨λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s), λ f g, Lp_to_Lp_restrict_add f g s,
    λ c f, Lp_to_Lp_restrict_smul c f s⟩
  1 (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le s f, })

variables {α F 𝕜}

variables (𝕜)
lemma Lp_to_Lp_restrict_clm_coe_fn [hp : fact (1 ≤ p)] (s : set α) (f : Lp F p μ) :
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

variables {ι : Type*} [normed_group E]

/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.small_sets`
along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma filter.tendsto.integral_sub_linear_is_o_ae
  [normed_space ℝ E] [complete_space E]
  {μ : measure α} {l : filter α} [l.is_measurably_generated]
  {f : α → E} {b : E} (h : tendsto f (l ⊓ μ.ae) (𝓝 b))
  (hfm : strongly_measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li l.small_sets)
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • b) m li :=
begin
  suffices : is_o (λ s, ∫ x in s, f x ∂μ - (μ s).to_real • b) (λ s, (μ s).to_real) l.small_sets,
    from (this.comp_tendsto hs).congr' (hsμ.mono $ λ a ha, ha ▸ rfl) hsμ,
  refine is_o_iff.2 (λ ε ε₀, _),
  have : ∀ᶠ s in l.small_sets, ∀ᶠ x in μ.ae, x ∈ s → f x ∈ closed_ball b ε :=
    eventually_small_sets_eventually.2 (h.eventually $ closed_ball_mem_nhds _ ε₀),
  filter_upwards [hμ.eventually, (hμ.integrable_at_filter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this],
  simp only [mem_closed_ball, dist_eq_norm],
  intros s hμs h_integrable hfm h_norm,
  rw [← set_integral_const, ← integral_sub h_integrable (integrable_on_const.2 $ or.inr hμs),
    real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
  exact norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub ae_strongly_measurable_const)
end

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).small_sets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_within_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [complete_space E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (ha : continuous_within_at f t a) (ht : measurable_set t)
  (hfm : strongly_measurable_at_filter f (𝓝[t] a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li (𝓝[t] a).small_sets)
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
by haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _;
exact (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae
  hfm (μ.finite_at_nhds_within a t) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).small_sets` along `li.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in
the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [complete_space E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α}
  {f : α → E} (ha : continuous_at f a) (hfm : strongly_measurable_at_filter f (𝓝 a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li (𝓝 a).small_sets)
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds a) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).small_sets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_on.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [complete_space E] [second_countable_topology_either α E]
  {μ : measure α} [is_locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (hft : continuous_on f t) (ha : a ∈ t) (ht : measurable_set t)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li (𝓝[t] a).small_sets)
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(hft a ha).integral_sub_linear_is_o_ae ht
  ⟨t, self_mem_nhds_within, hft.ae_strongly_measurable ht⟩ hs m hsμ

section
/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `continuous_linear_map.comp_Lp`. We take advantage of this construction here.
-/

open_locale complex_conjugate

variables {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  [normed_group F] [normed_space 𝕜 F]
  {p : ennreal}

namespace continuous_linear_map

variables [complete_space F] [normed_space ℝ F]

lemma integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) :
  ∫ a, (L.comp_Lp φ) a ∂μ = ∫ a, L (φ a) ∂μ :=
integral_congr_ae $ coe_fn_comp_Lp _ _

lemma set_integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) {s : set α} (hs : measurable_set s) :
  ∫ a in s, (L.comp_Lp φ) a ∂μ = ∫ a in s, L (φ a) ∂μ :=
set_integral_congr_ae hs ((L.coe_fn_comp_Lp φ).mono (λ x hx hx2, hx))

lemma continuous_integral_comp_L1 (L : E →L[𝕜] F) :
  continuous (λ (φ : α →₁[μ] E), ∫ (a : α), L (φ a) ∂μ) :=
by { rw ← funext L.integral_comp_Lp, exact continuous_integral.comp (L.comp_LpL 1 μ).continuous, }

variables [complete_space E] [normed_space ℝ E]

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

lemma integral_apply {H : Type*} [normed_group H] [normed_space 𝕜 H]
  {φ : α → H →L[𝕜] E} (φ_int : integrable φ μ) (v : H) :
  (∫ a, φ a ∂μ) v = ∫ a, φ a v ∂μ :=
((continuous_linear_map.apply 𝕜 E v).integral_comp_comm φ_int).symm

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

variables [complete_space F] [normed_space ℝ F] [complete_space E] [normed_space ℝ E]

lemma integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : α → E) : ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.to_continuous_linear_map.integral_comp_comm' L.antilipschitz _

end linear_isometry

variables [complete_space E] [normed_space ℝ E] [complete_space F] [normed_space ℝ F]

@[norm_cast] lemma integral_of_real {f : α → ℝ} : ∫ a, (f a : 𝕜) ∂μ = ↑∫ a, f a ∂μ :=
(@is_R_or_C.of_real_li 𝕜 _).integral_comp_comm f

lemma integral_re {f : α → 𝕜} (hf : integrable f μ) :
  ∫ a, is_R_or_C.re (f a) ∂μ = is_R_or_C.re ∫ a, f a ∂μ :=
(@is_R_or_C.re_clm 𝕜 _).integral_comp_comm hf

lemma integral_im {f : α → 𝕜} (hf : integrable f μ) :
  ∫ a, is_R_or_C.im (f a) ∂μ = is_R_or_C.im ∫ a, f a ∂μ :=
(@is_R_or_C.im_clm 𝕜 _).integral_comp_comm hf

lemma integral_conj {f : α → 𝕜} : ∫ a, conj (f a) ∂μ = conj ∫ a, f a ∂μ :=
(@is_R_or_C.conj_lie 𝕜 _).to_linear_isometry.integral_comp_comm f

lemma integral_coe_re_add_coe_im {f : α → 𝕜} (hf : integrable f μ) :
  ∫ x, (is_R_or_C.re (f x) : 𝕜) ∂μ + ∫ x, is_R_or_C.im (f x) ∂μ * is_R_or_C.I = ∫ x, f x ∂μ :=
begin
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add],
  { congr,
    ext1 x,
    rw [smul_eq_mul, mul_comm, is_R_or_C.re_add_im] },
  { exact hf.re.of_real },
  { exact hf.im.of_real.smul is_R_or_C.I }
end

lemma integral_re_add_im {f : α → 𝕜} (hf : integrable f μ) :
  ((∫ x, is_R_or_C.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, is_R_or_C.im (f x) ∂μ : ℝ) * is_R_or_C.I =
  ∫ x, f x ∂μ :=
by { rw [← integral_of_real, ← integral_of_real, integral_coe_re_add_coe_im hf] }

lemma set_integral_re_add_im {f : α → 𝕜} {i : set α} (hf : integrable_on f i μ) :
  ((∫ x in i, is_R_or_C.re (f x) ∂μ : ℝ) : 𝕜) +
  (∫ x in i, is_R_or_C.im (f x) ∂μ : ℝ) * is_R_or_C.I = ∫ x in i, f x ∂μ :=
integral_re_add_im hf

lemma fst_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ :=
((continuous_linear_map.fst ℝ E F).integral_comp_comm hf).symm

lemma snd_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ :=
((continuous_linear_map.snd ℝ E F).integral_comp_comm hf).symm

lemma integral_pair {f : α → E} {g : α → F} (hf : integrable f μ) (hg : integrable g μ) :
  ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
have _ := hf.prod_mk hg, prod.ext (fst_integral this) (snd_integral this)

lemma integral_smul_const {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] (f : α → 𝕜) (c : E) :
  ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c :=
begin
  by_cases hf : integrable f μ,
  { exact ((1 : 𝕜 →L[𝕜] 𝕜).smul_right c).integral_comp_comm hf },
  { by_cases hc : c = 0,
    { simp only [hc, integral_zero, smul_zero] },
    rw [integral_undef hf, integral_undef, zero_smul],
    simp_rw [integrable_smul_const hc, hf, not_false_iff] }
end

section inner

variables {E' : Type*} [inner_product_space 𝕜 E'] [complete_space E'] [normed_space ℝ E']

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E' _ x y

lemma integral_inner {f : α → E'} (hf : integrable f μ) (c : E') :
  ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
((@innerSL 𝕜 E' _ _ c).restrict_scalars ℝ).integral_comp_comm hf

lemma integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E') (hf : integrable f μ)
  (hf_int : ∀ (c : E'), ∫ x, ⟪c, f x⟫ ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }

end inner

lemma integral_with_density_eq_integral_smul
  {f : α → ℝ≥0} (f_meas : measurable f) (g : α → E) :
  ∫ a, g a ∂(μ.with_density (λ x, f x)) = ∫ a, f a • g a ∂μ :=
begin
  by_cases hg : integrable g (μ.with_density (λ x, f x)), swap,
  { rw [integral_undef hg, integral_undef],
    rwa [← integrable_with_density_iff_integrable_smul f_meas];
    apply_instance },
  refine integrable.induction _ _ _ _ _ hg,
  { assume c s s_meas hs,
    rw integral_indicator s_meas,
    simp_rw [← indicator_smul_apply, integral_indicator s_meas],
    simp only [s_meas, integral_const, measure.restrict_apply', univ_inter, with_density_apply],
    rw [lintegral_coe_eq_integral, ennreal.to_real_of_real, ← integral_smul_const],
    { refl },
    { exact integral_nonneg (λ x, nnreal.coe_nonneg _) },
    { refine ⟨(f_meas.coe_nnreal_real).ae_measurable.ae_strongly_measurable, _⟩,
      rw with_density_apply _ s_meas at hs,
      rw has_finite_integral,
      convert hs,
      ext1 x,
      simp only [nnreal.nnnorm_eq] } },
  { assume u u' h_disj u_int u'_int h h',
    change ∫ (a : α), (u a + u' a) ∂μ.with_density (λ (x : α), ↑(f x)) =
      ∫ (a : α), f a • (u a + u' a) ∂μ,
    simp_rw [smul_add],
    rw [integral_add u_int u'_int, h, h', integral_add],
    { exact (integrable_with_density_iff_integrable_smul f_meas).1 u_int },
    { exact (integrable_with_density_iff_integrable_smul f_meas).1 u'_int } },
  { have C1 : continuous (λ (u : Lp E 1 (μ.with_density (λ x, f x))),
      ∫ x, u x ∂(μ.with_density (λ x, f x))) := continuous_integral,
    have C2 : continuous (λ (u : Lp E 1 (μ.with_density (λ x, f x))),
      ∫ x, f x • u x ∂μ),
    { have : continuous ((λ (u : Lp E 1 μ), ∫ x, u x ∂μ) ∘ (with_density_smul_li μ f_meas)) :=
        continuous_integral.comp (with_density_smul_li μ f_meas).continuous,
      convert this,
      ext1 u,
      simp only [function.comp_app, with_density_smul_li_apply],
      exact integral_congr_ae (mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp.symm },
    exact is_closed_eq C1 C2 },
  { assume u v huv u_int hu,
    rw [← integral_congr_ae huv, hu],
    apply integral_congr_ae,
    filter_upwards [(ae_with_density_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx,
    rcases eq_or_ne (f x) 0 with h'x|h'x,
    { simp only [h'x, zero_smul]},
    { rw [hx _],
      simpa only [ne.def, ennreal.coe_eq_zero] using h'x } }
end

lemma integral_with_density_eq_integral_smul₀
  {f : α → ℝ≥0} (hf : ae_measurable f μ) (g : α → E) :
  ∫ a, g a ∂(μ.with_density (λ x, f x)) = ∫ a, f a • g a ∂μ :=
begin
  let f' := hf.mk _,
  calc ∫ a, g a ∂(μ.with_density (λ x, f x))
      = ∫ a, g a ∂(μ.with_density (λ x, f' x)) :
  begin
    congr' 1,
    apply with_density_congr_ae,
    filter_upwards [hf.ae_eq_mk] with x hx,
    rw hx,
  end
  ... = ∫ a, f' a • g a ∂μ : integral_with_density_eq_integral_smul hf.measurable_mk _
  ... = ∫ a, f a • g a ∂μ :
  begin
    apply integral_congr_ae,
    filter_upwards [hf.ae_eq_mk] with x hx,
    rw hx,
  end
end

lemma set_integral_with_density_eq_set_integral_smul
  {f : α → ℝ≥0} (f_meas : measurable f) (g : α → E) {s : set α} (hs : measurable_set s) :
  ∫ a in s, g a ∂(μ.with_density (λ x, f x)) = ∫ a in s, f a • g a ∂μ :=
by rw [restrict_with_density hs, integral_with_density_eq_integral_smul f_meas]

lemma set_integral_with_density_eq_set_integral_smul₀ {f : α → ℝ≥0} {s : set α}
  (hf : ae_measurable f (μ.restrict s)) (g : α → E) (hs : measurable_set s) :
  ∫ a in s, g a ∂(μ.with_density (λ x, f x)) = ∫ a in s, f a • g a ∂μ :=
by rw [restrict_with_density hs, integral_with_density_eq_integral_smul₀ hf]

end
