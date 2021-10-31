/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.constructions.borel_space

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ennreal.ae_measurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`measure_theory.ae_measurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/

open measure_theory set topological_space
open_locale classical ennreal nnreal

/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
theorem measure_theory.ae_measurable_of_exist_almost_disjoint_supersets
  {α : Type*} {m : measurable_space α} (μ : measure α)
  {β : Type*} [complete_linear_order β] [densely_ordered β] [topological_space β]
  [order_topology β] [second_countable_topology β] [measurable_space β] [borel_space β]
  (s : set β) (s_count : countable s) (s_dense : dense s) (f : α → β)
  (h : ∀ (p ∈ s) (q ∈ s), p < q → ∃ u v, measurable_set u ∧ measurable_set v ∧
    {x | f x < p} ⊆ u ∧ {x | q < f x} ⊆ v ∧ μ (u ∩ v) = 0) :
  ae_measurable f μ  :=
begin
  haveI : encodable s := s_count.to_encodable,
  have h' : ∀ p q, ∃ u v, measurable_set u ∧ measurable_set v ∧
    {x | f x < p} ⊆ u ∧ {x | q < f x} ⊆ v ∧ (p ∈ s → q ∈ s → p < q → μ (u ∩ v) = 0),
  { assume p q,
    by_cases H : p ∈ s ∧ q ∈ s ∧ p < q,
    { rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩,
      exact ⟨u, v, hu, hv, h'u, h'v, λ ps qs pq, hμ⟩ },
    { refine ⟨univ, univ, measurable_set.univ, measurable_set.univ, subset_univ _, subset_univ _,
        λ ps qs pq, _⟩,
      simp only [not_and] at H,
      exact (H ps qs pq).elim } },
  choose! u v huv using h',
  let u' : β → set α := λ p, ⋂ (q ∈ s ∩ Ioi p), u p q,
  have u'_meas : ∀ i, measurable_set (u' i),
  { assume i,
    exact measurable_set.bInter (s_count.mono (inter_subset_left _ _)) (λ b hb, (huv i b).1) },
  let f' : α → β := λ x, ⨅ (i : s), piecewise (u' i) (λ x, (i : β)) (λ x, (⊤ : β)) x,
  have f'_meas : measurable f',
  { apply measurable_infi,
    exact λ i, measurable.piecewise (u'_meas i) measurable_const measurable_const },
  let t := ⋃ (p : s) (q : s ∩ Ioi p), u' p ∩ v p q,
  have μt : μ t ≤ 0 := calc
    μ t ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u' p ∩ v p q) : begin
      refine (measure_Union_le _).trans _,
      apply ennreal.tsum_le_tsum (λ p, _),
      apply measure_Union_le _,
      exact (s_count.mono (inter_subset_left _ _)).to_encodable,
    end
    ... ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u p q ∩ v p q) : begin
      apply ennreal.tsum_le_tsum (λ p, _),
      refine ennreal.tsum_le_tsum (λ q, measure_mono _),
      exact inter_subset_inter_left _ (bInter_subset_of_mem q.2)
    end
    ... = ∑' (p : s) (q : s ∩ Ioi p), (0 : ℝ≥0∞) :
      by { congr, ext1 p, congr, ext1 q, exact (huv p q).2.2.2.2 p.2 q.2.1 q.2.2 }
    ... = 0 : by simp only [tsum_zero],
  have ff' : ∀ᵐ x ∂μ, f x = f' x,
  { have : ∀ᵐ x ∂μ, x ∉ t,
    { have : μ t = 0 := le_antisymm μt bot_le,
      change μ _ = 0,
      convert this,
      ext y,
      simp only [not_exists, exists_prop, mem_set_of_eq, mem_compl_eq, not_not_mem] },
    filter_upwards [this],
    assume x hx,
    apply (infi_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm,
    { assume i,
      by_cases H : x ∈ u' i,
      swap, { simp only [H, le_top, not_false_iff, piecewise_eq_of_not_mem] },
      simp only [H, piecewise_eq_of_mem],
      contrapose! hx,
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (i : β) (f x) ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) is_open_Ioo (nonempty_Ioo.2 hx),
      have A : x ∈ v i r := (huv i r).2.2.2.1 rq,
      apply mem_Union.2 ⟨i, _⟩,
      refine mem_Union.2 ⟨⟨r, ⟨rs, xr⟩⟩, _⟩,
      exact ⟨H, A⟩ },
    { assume q hq,
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (f x) q ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) is_open_Ioo (nonempty_Ioo.2 hq),
      refine ⟨⟨r, rs⟩, _⟩,
      have A : x ∈ u' r := mem_bInter (λ i hi, (huv r i).2.2.1 xr),
      simp only [A, rq, piecewise_eq_of_mem, subtype.coe_mk] } },
  exact ⟨f', f'_meas, ff'⟩,
end

/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
theorem ennreal.ae_measurable_of_exist_almost_disjoint_supersets
  {α : Type*} {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞)
  (h : ∀ (p : ℝ≥0) (q : ℝ≥0), p < q → ∃ u v, measurable_set u ∧ measurable_set v ∧
    {x | f x < p} ⊆ u ∧ {x | (q : ℝ≥0∞) < f x} ⊆ v ∧ μ (u ∩ v) = 0) :
  ae_measurable f μ :=
begin
  let s : set ℝ≥0∞ := {x | ∃ a : ℚ, x = ennreal.of_real a},
  have s_count : countable s,
  { have : s = range (λ (a : ℚ), ennreal.of_real a),
      by { ext x, simp only [eq_comm, mem_range, mem_set_of_eq] },
    rw this,
    exact countable_range _ },
  have s_dense : dense s,
  { refine dense_iff_forall_lt_exists_mem.2 (λ c d hcd, _),
    rcases ennreal.lt_iff_exists_rat_btwn.1 hcd with ⟨q, hq⟩,
    exact ⟨ennreal.of_real q, ⟨q, rfl⟩, hq.2⟩ },
  apply measure_theory.ae_measurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _,
  rintros _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq,
  apply h,
  simpa [ennreal.of_real] using hpq,
end
