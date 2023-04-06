/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import measure_theory.measure.regular
import measure_theory.function.simple_func_dense_lp
import topology.urysohns_lemma
import measure_theory.integral.bochner

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `1 ≤ p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.
It also proves the same results for approximation by continuous functions with compact support
when the space is locally compact and `μ` is regular.

The result is presented in several versions. First concrete versions giving an approximation
up to `ε` in these various contexts, and then abstract versions stating that the topological
closure of the relevant subgroups of `Lp` are the whole space.

* `mem_ℒp.exists_has_compact_support_snorm_sub_le` states that, in a locally compact space,
  an `ℒp` function can be approximated by continuous functions with compact support,
  in the sense that `snorm (f - g) p μ` is small.
* `mem_ℒp.exists_has_compact_support_integral_rpow_sub_le`: same result, but expressed in
  terms of `∫ ‖f - g‖^p`.

Versions with `integrable` instead of `mem_ℒp` are specialized to the case `p = 1`.
Versions with `bounded_continuous` instead of `has_compact_support` drop the locally
compact assumption and give only approximation by a bounded continuous function.

* `measure_theory.Lp.bounded_continuous_function_dense`: The subgroup
  `measure_theory.Lp.bounded_continuous_function` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `bounded_continuous_function.to_Lp_dense_range`: For finite-measure `μ`, the continuous linear
  map `bounded_continuous_function.to_Lp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `continuous_map.to_Lp_dense_range`: For compact `α` and finite-measure `μ`, the continuous linear
  map `continuous_map.to_Lp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?  See the
Vitali-Carathéodory theorem, in the file `measure_theory.vitali_caratheodory`.

-/

open_locale ennreal nnreal topology bounded_continuous_function
open measure_theory topological_space continuous_map set

variables {α : Type*} [measurable_space α] [topological_space α] [normal_space α] [borel_space α]
variables {E : Type*} [normed_add_comm_group E] {μ : measure α} {p : ℝ≥0∞}

namespace measure_theory

variables [normed_space ℝ E]

/-- A variant of Urysohn's lemma, `ℒ^p` version, for an outer regular measure `μ`:
consider two sets `s ⊆ u` which are respectively closed and open with `μ s < ∞`, and a vector `c`.
Then one may find a continuous function `f` equal to `c` on `s` and to `0` outside of `u`,
bounded by `‖c‖` everywhere, and such that the `ℒ^p` norm of `f - s.indicator (λ y, c)` is
arbitrarily small. Additionally, this function `f` belongs to `ℒ^p`. -/
lemma exists_continuous_snorm_sub_le_of_closed [μ.outer_regular]
  (hp : p ≠ ∞) {s u : set α} (s_closed : is_closed s) (u_open : is_open u) (hsu : s ⊆ u)
  (hs : μ s ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (f : α → E), snorm (λ x, f x - s.indicator (λ y, c) x) p μ ≤ ε ∧
    continuous f ∧ (∀ x, ‖f x‖ ≤ ‖c‖) ∧ function.support f ⊆ u ∧ mem_ℒp f p μ :=
begin
  rcases exists_snorm_indicator_le hp c hε with ⟨η, η_pos, hη⟩,
  have ηpos : (0 : ℝ≥0∞) < η := ennreal.coe_lt_coe.2 η_pos,
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : set α) (H : V ⊇ s), is_open V ∧ μ V < ∞ ∧ μ (V \ s) < η,
    from s_closed.measurable_set.exists_is_open_diff_lt hs ηpos.ne',
  let v := u ∩ V,
  have hsv : s ⊆ v := subset_inter hsu sV,
  have hμv : μ v < ∞ := (measure_mono (inter_subset_right _ _)).trans_lt h'V,
  obtain ⟨g, hgv, hgs, hg_range⟩ := exists_continuous_zero_one_of_closed
    (u_open.inter V_open).is_closed_compl s_closed (disjoint_compl_left_iff.2 hsv),
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `v \ s`, which has small measure.
  have g_norm : ∀ x, ‖g x‖ = g x := λ x, by rw [real.norm_eq_abs, abs_of_nonneg (hg_range x).1],
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖,
  { assume x,
    simp only [norm_smul, g_norm x],
    apply mul_le_of_le_one_left (norm_nonneg _),
    exact (hg_range x).2 },
  have gc_bd : ∀ x, ‖g x • c - s.indicator (λ x, c) x‖ ≤ ‖(v \ s).indicator (λ x, c) x‖,
  { intros x,
    by_cases hv : x ∈ v,
    { rw ← set.diff_union_of_subset hsv at hv,
      cases hv with hsv hs,
      { simpa only [hsv.2, set.indicator_of_not_mem, not_false_iff, sub_zero, hsv,
          set.indicator_of_mem] using gc_bd0 x},
      { simp [hgs hs, hs] } },
    { simp [hgv hv, (λ h, hv (hsv h) : x ∉ s)], } },
  have gc_support : function.support (λ (x : α), g x • c) ⊆ v,
  { refine function.support_subset_iff'.2 (λ x hx, _),
    simp only [hgv hx, pi.zero_apply, zero_smul] },
  have gc_mem : mem_ℒp (λ x, g x • c) p μ,
  { apply mem_ℒp.smul_of_top_left (mem_ℒp_top_const _),
    refine ⟨g.continuous.ae_strongly_measurable, _⟩,
    have : snorm (v.indicator (λ x, (1 : ℝ))) p μ < ⊤,
    { refine (snorm_indicator_const_le _ _).trans_lt _,
      simp only [lt_top_iff_ne_top, hμv.ne, nnnorm_one, ennreal.coe_one, one_div, one_mul, ne.def,
        ennreal.rpow_eq_top_iff, inv_lt_zero, false_and, or_false, not_and, not_lt,
        ennreal.to_real_nonneg, implies_true_iff] },
    refine (snorm_mono (λ x, _)).trans_lt this,
    by_cases hx : x ∈ v,
    { simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, real.norm_eq_abs,
        indicator_of_mem, cstar_ring.norm_one] },
    { simp only [hgv hx, pi.zero_apply, real.norm_eq_abs, abs_zero, abs_nonneg] } },
  refine ⟨λ x, g x • c, (snorm_mono gc_bd).trans _, g.continuous.smul continuous_const, gc_bd0,
    gc_support.trans (inter_subset_left _ _), gc_mem⟩,
  exact hη _ ((measure_mono (diff_subset_diff (inter_subset_right _ _) subset.rfl)).trans hV.le),
end

/-- In a locally compact space, any function in `ℒp` can be approximated by compactly supported
continuous functions when `1 ≤ p < ∞`, version in terms of `snorm`. -/
lemma mem_ℒp.exists_has_compact_support_snorm_sub_le
  [locally_compact_space α] [μ.regular] (hp : p ≠ ∞) (h'p : 1 ≤ p)
  {f : α → E} (hf : mem_ℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α → E), snorm (f - g) p μ ≤ ε ∧ continuous g ∧ mem_ℒp g p μ ∧ has_compact_support g :=
begin
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and consists of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp h'p _ _ _ _ hε, rotate,
  { rintros f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩,
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩ },
  { rintros f ⟨f_cont, f_mem, hf⟩,
    exact f_mem.ae_strongly_measurable },
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_snorm_sub_le_of_closed`.
  assume c t ht htμ ε hε,
  have h'ε : ε / 2 ≠ 0, by simpa using hε,
  rcases exists_snorm_indicator_le hp c h'ε with ⟨η, ηpos, hη⟩,
  have hη_pos' : (0 : ℝ≥0∞) < η, from ennreal.coe_pos.2 ηpos,
  obtain ⟨s, st, s_compact, μs⟩ : ∃ s ⊆ t, is_compact s ∧ μ (t \ s) < η,
    from ht.exists_is_compact_diff_lt htμ.ne hη_pos'.ne',
  have hsμ : μ s < ∞, from (measure_mono st).trans_lt htμ,
  have I1 : snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ ≤ ε/2,
  { rw [← snorm_neg, neg_sub, ← indicator_diff st],
    exact (hη _ μs.le) },
  rcases exists_compact_between s_compact is_open_univ (subset_univ _) with ⟨k, k_compact, sk, -⟩,
  rcases exists_continuous_snorm_sub_le_of_closed hp s_compact.is_closed is_open_interior sk
    hsμ.ne c h'ε with ⟨f, I2, f_cont, f_bound, f_support, f_mem⟩,
  have I3 : snorm (f - t.indicator (λ y, c)) p μ ≤ ε, from calc
    snorm (f - t.indicator (λ y, c)) p μ
      = snorm ((f - s.indicator (λ y, c)) + (s.indicator (λ y, c) - t.indicator (λ y, c))) p μ :
    by simp only [sub_add_sub_cancel]
  ... ≤ snorm (f - s.indicator (λ y, c)) p μ
        + snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ :
    begin
      refine snorm_add_le _ _ h'p,
      { exact f_mem.ae_strongly_measurable.sub
          (ae_strongly_measurable_const.indicator s_compact.measurable_set) },
      { exact (ae_strongly_measurable_const.indicator s_compact.measurable_set).sub
          (ae_strongly_measurable_const.indicator ht) },
    end
  ... ≤ ε/2 + ε/2 : add_le_add I2 I1
  ... = ε : ennreal.add_halves _,
  refine ⟨f, I3, f_cont, f_mem, has_compact_support.intro k_compact (λ x hx, _)⟩,
  rw ← function.nmem_support,
  contrapose! hx,
  exact interior_subset (f_support hx)
end

/-- In a locally compact space, any function in `ℒp` can be approximated by compactly supported
continuous functions when `1 ≤ p < ∞`, version in terms of `∫`. -/
lemma mem_ℒp.exists_has_compact_support_integral_rpow_sub_le
  [locally_compact_space α] [μ.regular] {p : ℝ} (h'p : 1 ≤ p)
  {f : α → E} (hf : mem_ℒp f (ennreal.of_real p) μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : α → E), ∫ x, ‖f x - g x‖^p ∂μ ≤ ε ∧ continuous g ∧ mem_ℒp g (ennreal.of_real p) μ
    ∧ has_compact_support g :=
begin
  have I : 0 < ε ^ (1/p) := real.rpow_pos_of_pos hε _,
  have A : ennreal.of_real (ε ^ (1/p)) ≠ 0,
    by simp only [ne.def, ennreal.of_real_eq_zero, not_le, I],
  have B : 1 ≤ ennreal.of_real p,
  { convert ennreal.of_real_le_of_real h'p, exact ennreal.of_real_one.symm },
  rcases hf.exists_has_compact_support_snorm_sub_le ennreal.coe_ne_top B A
    with ⟨g, hg, g_cont, g_mem, g_support⟩,
  change snorm _ (ennreal.of_real p) _ ≤ _ at hg,
  refine ⟨g, _, g_cont, g_mem, g_support⟩,
  rwa [(hf.sub g_mem).snorm_eq_integral_rpow_norm (zero_lt_one.trans_le B).ne'
    ennreal.coe_ne_top, ennreal.of_real_le_of_real_iff I.le, one_div,
    ennreal.to_real_of_real (zero_le_one.trans h'p), real.rpow_le_rpow_iff _ hε.le _] at hg,
  { exact integral_nonneg (λ x, real.rpow_nonneg_of_nonneg (norm_nonneg _) _) },
  { exact inv_pos.2 (zero_lt_one.trans_le h'p) }
end

/-- In a locally compact space, any integrable function can be approximated by compactly supported
continuous functions, version in terms of `∫⁻`. -/
lemma integrable.exists_has_compact_support_lintegral_sub_le [locally_compact_space α] [μ.regular]
  {f : α → E} (hf : integrable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α → E), ∫⁻ x, ‖f x - g x‖₊ ∂μ ≤ ε ∧ continuous g ∧ integrable g μ
    ∧ has_compact_support g :=
begin
  simp only [← mem_ℒp_one_iff_integrable, ← snorm_one_eq_lintegral_nnnorm] at hf ⊢,
  exact hf.exists_has_compact_support_snorm_sub_le ennreal.one_ne_top le_rfl hε,
end

/-- In a locally compact space, any integrable function can be approximated by compactly supported
continuous functions, version in terms of `∫`. -/
lemma integrable.exists_has_compact_support_integral_sub_le [locally_compact_space α] [μ.regular]
  {f : α → E} (hf : integrable f μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : α → E), ∫ x, ‖f x - g x‖ ∂μ ≤ ε ∧ continuous g ∧ integrable g μ
    ∧ has_compact_support g :=
begin
  simp only [← mem_ℒp_one_iff_integrable, ← snorm_one_eq_lintegral_nnnorm,
    ← ennreal.of_real_one] at hf ⊢,
  simpa using hf.exists_has_compact_support_integral_rpow_sub_le le_rfl hε,
end

/-- Any function in `ℒp` can be approximated by bounded continuous functions when `1 ≤ p < ∞`,
version in terms of `snorm`. -/
lemma mem_ℒp.exists_bounded_continuous_snorm_sub_le [μ.weakly_regular] (hp : p ≠ ∞) (h'p : 1 ≤ p)
  {f : α → E} (hf : mem_ℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α →ᵇ E), snorm (f - g) p μ ≤ ε ∧ mem_ℒp g p μ :=
begin
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and made of ae strongly measurable functions.
  -- First check the latter easy facts.
  suffices H : ∃ (g : α → E), snorm (f - g) p μ ≤ ε ∧ continuous g ∧ mem_ℒp g p μ ∧
    metric.bounded (range g),
  { rcases H with ⟨g, hg, g_cont, g_mem, g_bd⟩,
    exact ⟨⟨⟨g, g_cont⟩, metric.bounded_range_iff.1 g_bd⟩, hg, g_mem⟩ },
  apply hf.induction_dense hp h'p _ _ _ _ hε, rotate,
  { rintros f g ⟨f_cont, f_mem, f_bd⟩ ⟨g_cont, g_mem, g_bd⟩,
    refine ⟨f_cont.add g_cont, f_mem.add g_mem, _⟩,
    let f' : α →ᵇ E := ⟨⟨f, f_cont⟩, metric.bounded_range_iff.1 f_bd⟩,
    let g' : α →ᵇ E := ⟨⟨g, g_cont⟩, metric.bounded_range_iff.1 g_bd⟩,
    exact (f' + g').bounded_range },
  { exact λ f ⟨_, h, _⟩, h.ae_strongly_measurable },
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_snorm_sub_le_of_closed`.
  assume c t ht htμ ε hε,
  have h'ε : ε / 2 ≠ 0, by simpa using hε,
  rcases exists_snorm_indicator_le hp c h'ε with ⟨η, ηpos, hη⟩,
  have hη_pos' : (0 : ℝ≥0∞) < η, from ennreal.coe_pos.2 ηpos,
  obtain ⟨s, st, s_closed, μs⟩ : ∃ s ⊆ t, is_closed s ∧ μ (t \ s) < η,
    from ht.exists_is_closed_diff_lt htμ.ne hη_pos'.ne',
  have hsμ : μ s < ∞, from (measure_mono st).trans_lt htμ,
  have I1 : snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ ≤ ε/2,
  { rw [← snorm_neg, neg_sub, ← indicator_diff st],
    exact (hη _ μs.le) },
  rcases exists_continuous_snorm_sub_le_of_closed hp s_closed is_open_univ (subset_univ _)
    hsμ.ne c h'ε with ⟨f, I2, f_cont, f_bound, -, f_mem⟩,
  have I3 : snorm (f - t.indicator (λ y, c)) p μ ≤ ε, from calc
    snorm (f - t.indicator (λ y, c)) p μ
      = snorm ((f - s.indicator (λ y, c)) + (s.indicator (λ y, c) - t.indicator (λ y, c))) p μ :
    by simp only [sub_add_sub_cancel]
  ... ≤ snorm (f - s.indicator (λ y, c)) p μ
        + snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ :
    begin
      refine snorm_add_le _ _ h'p,
      { exact f_mem.ae_strongly_measurable.sub
          (ae_strongly_measurable_const.indicator s_closed.measurable_set) },
      { exact (ae_strongly_measurable_const.indicator s_closed.measurable_set).sub
          (ae_strongly_measurable_const.indicator ht) },
    end
  ... ≤ ε/2 + ε/2 : add_le_add I2 I1
  ... = ε : ennreal.add_halves _,
  refine ⟨f, I3, f_cont, f_mem, _⟩,
  exact (bounded_continuous_function.of_normed_add_comm_group f f_cont _ f_bound).bounded_range,
end

/-- Any function in `ℒp` can be approximated by bounded continuous functions when `1 ≤ p < ∞`,
version in terms of `∫`. -/
lemma mem_ℒp.exists_bounded_continuous_integral_rpow_sub_le
  [μ.weakly_regular] {p : ℝ} (h'p : 1 ≤ p)
  {f : α → E} (hf : mem_ℒp f (ennreal.of_real p) μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : α →ᵇ E), ∫ x, ‖f x - g x‖^p ∂μ ≤ ε ∧ mem_ℒp g (ennreal.of_real p) μ :=
begin
  have I : 0 < ε ^ (1/p) := real.rpow_pos_of_pos hε _,
  have A : ennreal.of_real (ε ^ (1/p)) ≠ 0,
    by simp only [ne.def, ennreal.of_real_eq_zero, not_le, I],
  have B : 1 ≤ ennreal.of_real p,
  { convert ennreal.of_real_le_of_real h'p, exact ennreal.of_real_one.symm },
  rcases hf.exists_bounded_continuous_snorm_sub_le ennreal.coe_ne_top B A
    with ⟨g, hg, g_mem⟩,
  change snorm _ (ennreal.of_real p) _ ≤ _ at hg,
  refine ⟨g, _, g_mem⟩,
  rwa [(hf.sub g_mem).snorm_eq_integral_rpow_norm (zero_lt_one.trans_le B).ne'
    ennreal.coe_ne_top, ennreal.of_real_le_of_real_iff I.le, one_div,
    ennreal.to_real_of_real (zero_le_one.trans h'p), real.rpow_le_rpow_iff _ hε.le _] at hg,
  { exact integral_nonneg (λ x, real.rpow_nonneg_of_nonneg (norm_nonneg _) _) },
  { exact inv_pos.2 (zero_lt_one.trans_le h'p) }
end

/-- Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫⁻`. -/
lemma integrable.exists_bounded_continuous_lintegral_sub_le [μ.weakly_regular]
  {f : α → E} (hf : integrable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α →ᵇ E), ∫⁻ x, ‖f x - g x‖₊ ∂μ ≤ ε ∧ integrable g μ :=
begin
  simp only [← mem_ℒp_one_iff_integrable, ← snorm_one_eq_lintegral_nnnorm] at hf ⊢,
  exact hf.exists_bounded_continuous_snorm_sub_le ennreal.one_ne_top le_rfl hε,
end

/-- Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫`. -/
lemma integrable.exists_bounded_continuous_integral_sub_le [μ.weakly_regular]
  {f : α → E} (hf : integrable f μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : α →ᵇ E), ∫ x, ‖f x - g x‖ ∂μ ≤ ε ∧ integrable g μ :=
begin
  simp only [← mem_ℒp_one_iff_integrable, ← snorm_one_eq_lintegral_nnnorm,
    ← ennreal.of_real_one] at hf ⊢,
  simpa using hf.exists_bounded_continuous_integral_rpow_sub_le le_rfl hε,
end

namespace Lp

variables (E)

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma bounded_continuous_function_dense
  [second_countable_topology_either α E] [_i : fact (1 ≤ p)] (hp : p ≠ ∞) [μ.weakly_regular] :
  (bounded_continuous_function E p μ).topological_closure = ⊤ :=
begin
  rw add_subgroup.eq_top_iff',
  assume f,
  refine mem_closure_iff_frequently.mpr _,
  rw metric.nhds_basis_closed_ball.frequently_iff,
  intros ε hε,
  have A : ennreal.of_real ε ≠ 0, by simp only [ne.def, ennreal.of_real_eq_zero, not_le, hε],
  obtain ⟨g, hg, g_mem⟩ : ∃ (g : α →ᵇ E), snorm (f - g) p μ ≤ ennreal.of_real ε ∧ mem_ℒp g p μ,
    from (Lp.mem_ℒp f).exists_bounded_continuous_snorm_sub_le hp _i.out A,
  refine ⟨g_mem.to_Lp _, _, ⟨g, rfl⟩⟩,
  simp only [dist_eq_norm, metric.mem_closed_ball'],
  rw Lp.norm_def,
  convert ennreal.to_real_le_of_le_of_real hε.le hg using 2,
  apply snorm_congr_ae,
  filter_upwards [coe_fn_sub f (g_mem.to_Lp g), g_mem.coe_fn_to_Lp] with x hx h'x,
  simp only [hx, pi.sub_apply, sub_right_inj, h'x],
end

end Lp

end measure_theory

variables [second_countable_topology_either α E] [_i : fact (1 ≤ p)] (hp : p ≠ ∞)
variables (𝕜 : Type*) [normed_field 𝕜] [normed_algebra ℝ 𝕜] [normed_space 𝕜 E]
include _i hp
variables (E) (μ)

namespace bounded_continuous_function

lemma to_Lp_dense_range [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (linear_map.range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ))
    .to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp],
end

end bounded_continuous_function

namespace continuous_map

lemma to_Lp_dense_range [compact_space α] [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (linear_map.range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ))
    .to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp]
end

end continuous_map
