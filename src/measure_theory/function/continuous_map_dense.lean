/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import measure_theory.measure.regular
import measure_theory.function.simple_func_dense_lp
import topology.urysohns_lemma

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `1 ≤ p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.

The result is presented in several versions:
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
open measure_theory topological_space continuous_map

variables {α : Type*} [measurable_space α] [topological_space α] [normal_space α] [borel_space α]
variables {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E]

open set

lemma glouk0 (μ : measure α) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
  ∃ (η : ℝ≥0), 0 < η ∧ ∀ (s : set α), μ s ≤ η → snorm (s.indicator (λ x, ‖c‖)) p μ ≤ ε :=
begin
  rcases eq_or_ne p 0 with rfl|h'p,
  { exact ⟨1, zero_lt_one, λ s hs, by simp⟩ },
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p,
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one ennreal.to_real_nonneg,
  have hp₀'' : 0 < p.to_real,
  { simpa [← ennreal.to_real_lt_to_real ennreal.zero_ne_top hp] using hp₀ },
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ (η : ℝ≥0), 0 < η ∧ (‖c‖₊ * η ^ (1 / p.to_real) : ℝ≥0∞) ≤ ε,
  { have : filter.tendsto (λ x : ℝ≥0, ((‖c‖₊ * x ^ (1 / p.to_real) : ℝ≥0) : ℝ≥0∞)) (𝓝 0) (𝓝 (0 : ℝ≥0)),
    { rw ennreal.tendsto_coe,
      convert ((nnreal.continuous_at_rpow_const (or.inr hp₀')).tendsto).const_mul _,
      simp [hp₀''.ne'] },
    have hε' : 0 < ε := hε.bot_lt,
    obtain ⟨δ, hδ, hδε'⟩ :=
      nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this),
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ,
    refine ⟨η, hη, _⟩,
    rw [ennreal.coe_rpow_of_nonneg _ hp₀', ← ennreal.coe_mul],
    exact hδε' hηδ },
  refine ⟨η, hη_pos, λ s hs, _⟩,
  refine (snorm_indicator_const_le _ _).trans (le_trans _ hη_le),
  simp only [nnnorm_norm],
  exact mul_le_mul_left' (ennreal.rpow_le_rpow hs hp₀') _,
end

lemma glouk {s u : set α} (s_closed : is_closed s) (u_open : is_open u) (hsu : s ⊆ u) (c : E) :
  ∃ (f : α → E), continuous f ∧ (∀ x, ‖f x‖ ≤ ‖c‖) ∧ function.support f ⊆ u
    ∧ ∀ x, ‖f x - s.indicator (λ y, c) x‖ ≤ ‖(u \ s).indicator (λ y, ‖c‖) x‖ :=
begin
  obtain ⟨g, hgu, hgs, hg_range⟩ := exists_continuous_zero_one_of_closed
    u_open.is_closed_compl s_closed (disjoint_compl_left_iff.2 hsu),
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `u \ s`
  have g_norm : ∀ x, ‖g x‖ = g x := λ x, by rw [real.norm_eq_abs, abs_of_nonneg (hg_range x).1],
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖,
  { assume x,
    simp only [norm_smul, g_norm x],
    apply mul_le_of_le_one_left (norm_nonneg _),
    exact (hg_range x).2 },
  have gc_bd : ∀ x, ‖g x • c - s.indicator (λ x, c) x‖ ≤ ‖(u \ s).indicator (λ x, ‖c‖) x‖,
  { intros x,
    by_cases hu : x ∈ u,
    { rw ← set.diff_union_of_subset hsu at hu,
      cases hu with hsu hs,
      { simpa only [hsu.2, set.indicator_of_not_mem, not_false_iff, sub_zero, hsu,
          set.indicator_of_mem, norm_norm] using gc_bd0 x },
      { simp [hgs hs, hs] } },
    { have : x ∉ s := λ h, hu (hsu h),
      simp [hgu hu, this] } },
  have gc_support : function.support (λ (x : α), g x • c) ⊆ u,
  { refine function.support_subset_iff'.2 (λ x hx, _),
    simp only [hgu hx, pi.zero_apply, zero_smul] },
  exact ⟨λ x, g x • c, g.continuous.smul continuous_const, gc_bd0, gc_support, gc_bd⟩,
end

lemma glouk2 {s u : set α} (s_closed : is_closed s) (u_open : is_open u) (hsu : s ⊆ u)
  (μ : measure α) [μ.outer_regular] (hs : μ s ≠ ∞) (c : E)
  {p : ℝ≥0∞} (hp : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (f : α → E), continuous f ∧ (∀ x, ‖f x‖ ≤ ‖c‖) ∧ function.support f ⊆ u
    ∧ snorm (λ x, f x - s.indicator (λ y, c) x) p μ ≤ ε :=
begin
  rcases glouk0 μ c hε hp with ⟨η, η_pos, hη⟩,
  have ηpos : (0 : ℝ≥0∞) < η := ennreal.coe_lt_coe.2 η_pos,
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : set α) (H : V ⊇ s), is_open V ∧ μ V < ∞ ∧ μ (V \ s) < η,
    from s_closed.measurable_set.exists_is_open_diff_lt hs ηpos.ne',
  rcases glouk s_closed (u_open.inter V_open) (subset_inter hsu sV) c
    with ⟨f, f_cont, f_bound, f_support, hf⟩,
  refine ⟨f, f_cont, f_bound, f_support.trans (inter_subset_left _ _), (snorm_mono hf).trans _⟩,
  apply hη,
  exact (measure_mono (diff_subset_diff (inter_subset_right _ _) subset.rfl)).trans hV.le,
end


variables [second_countable_topology_either α E]  {p : ℝ≥0∞} [_i : fact (1 ≤ p)] (hp : p ≠ ∞)
  (μ : measure α)

variable {E}

include _i hp

namespace measure_theory.Lp

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma bounded_continuous_function_dense [μ.weakly_regular] :
  (bounded_continuous_function E p μ).topological_closure = ⊤ :=
begin
  -- It suffices to prove that scalar multiples of the indicator function of a finite-measure
  -- measurable set can be approximated by continuous functions
  suffices :  ∀ (c : E) {s : set α} (hs : measurable_set s) (hμs : μ s < ∞),
    (Lp.simple_func.indicator_const p hs hμs.ne c : Lp E p μ)
      ∈ (bounded_continuous_function E p μ).topological_closure,
  sorry{ rw add_subgroup.eq_top_iff',
    refine Lp.induction hp _ _ _ _,
    { exact this },
    { exact λ f g hf hg hfg', add_subgroup.add_mem _ },
    { exact add_subgroup.is_closed_topological_closure _ } },
  -- Let `s` be a finite-measure measurable set, let's approximate `c` times its indicator function
  intros c t ht htμ,
  refine mem_closure_iff_frequently.mpr _,
  rw metric.nhds_basis_closed_ball.frequently_iff,
  intros ε hε,
  let ε' : ℝ≥0 := ⟨ε, hε.le⟩,
  have h'ε : (ε' / 2 : ℝ≥0∞) ≠ 0, by simpa only [ne.def, ennreal.div_zero_iff, ennreal.coe_eq_zero,
    nonneg.mk_eq_zero, ennreal.bit0_eq_top_iff, ennreal.one_ne_top, or_false] using hε.ne',
  rcases glouk0 μ c h'ε hp with ⟨η, ηpos, hη⟩,
  have hη_pos' : (0 : ℝ≥0∞) < η := ennreal.coe_pos.2 ηpos,
  obtain ⟨s, st, s_closed, μs⟩ : ∃ s ⊆ t, is_closed s ∧ μ (t \ s) < η :=
    ht.exists_is_closed_diff_lt htμ.ne hη_pos'.ne',
  have : snorm (t.indicator (λ y, c) - s.indicator (λ y, c)) p μ ≤ ε'/2,
  { rw ← indicator_diff st,
    apply le_trans (le_of_eq _) (hη _ μs.le),
    rw [← snorm_norm, indicator_comp_of_zero _root_.norm_zero] },
    obtain ⟨u, su, u_open, μu⟩ : ∃ u ⊇ s, is_open u ∧ μ (u \ s) < η,
  { have Z := s_closed.measurable_set.exists_is_open_diff_lt,
    simpa using ennreal.add_lt_add_left hsμ.ne hη_pos' },

end

#exit


  have : disjoint uᶜ s := (st.trans tu).disjoint_compl_left,
  have h_μ_sdiff : μ (u \ s) ≤ 2 * η,
  sorry { have hsμ : μ s < ⊤ := (measure_mono st).trans_lt htμ,
    refine ennreal.le_of_add_le_add_left hsμ.ne _,
    have : μ u < μ s + ↑η + ↑η,
      from μu.trans (ennreal.add_lt_add_right ennreal.coe_ne_top μs),
    convert this.le using 1,
    { rw [add_comm, ← measure_union, set.diff_union_of_subset (st.trans tu)],
      exacts [disjoint_sdiff_self_left, s_closed.measurable_set] },
    have : (2:ℝ≥0∞) * η = η + η := by simpa using add_mul (1:ℝ≥0∞) 1 η,
    rw this,
    abel },


end

#exit

  -- A little bit of pre-emptive work, to find `η : ℝ≥0` which will be a margin small enough for
  -- our purposes
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η, 0 < η ∧ (↑(‖bit0 (‖c‖)‖₊ * (2 * η) ^ (1 / p.to_real)) : ℝ) ≤ ε,
  { have : filter.tendsto (λ x : ℝ≥0, ‖bit0 (‖c‖)‖₊ * (2 * x) ^ (1 / p.to_real)) (𝓝 0) (𝓝 0),
    { have : filter.tendsto (λ x : ℝ≥0, 2 * x) (𝓝 0) (𝓝 (2 * 0)) := filter.tendsto_id.const_mul 2,
      convert ((nnreal.continuous_at_rpow_const (or.inr hp₀')).tendsto.comp this).const_mul _,
      simp [hp₀''.ne'] },
    let ε' : ℝ≥0 := ⟨ε, hε.le⟩,
    have hε' : 0 < ε' := by exact_mod_cast hε,
    obtain ⟨δ, hδ, hδε'⟩ :=
      nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this),
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ,
    refine ⟨η, hη, _⟩,
    exact_mod_cast hδε' hηδ },
  have hη_pos' : (0 : ℝ≥0∞) < η := ennreal.coe_pos.2 hη_pos,
  -- Use the regularity of the measure to `η`-approximate `s` by an open superset and a closed
  -- subset
  obtain ⟨u, su, u_open, μu⟩ : ∃ u ⊇ s, is_open u ∧ μ u < μ s + ↑η,
  { refine s.exists_is_open_lt_of_lt _ _,
    simpa using ennreal.add_lt_add_left hsμ.ne hη_pos' },
  obtain ⟨F, Fs, F_closed, μF⟩ : ∃ F ⊆ s, is_closed F ∧ μ s < μ F + ↑η :=
    hs.exists_is_closed_lt_add hsμ.ne hη_pos'.ne',
  have : disjoint uᶜ F := (Fs.trans su).disjoint_compl_left,
  have h_μ_sdiff : μ (u \ F) ≤ 2 * η,
  { have hFμ : μ F < ⊤ := (measure_mono Fs).trans_lt hsμ,
    refine ennreal.le_of_add_le_add_left hFμ.ne _,
    have : μ u < μ F + ↑η + ↑η,
      from μu.trans (ennreal.add_lt_add_right ennreal.coe_ne_top μF),
    convert this.le using 1,
    { rw [add_comm, ← measure_union, set.diff_union_of_subset (Fs.trans su)],
      exacts [disjoint_sdiff_self_left, F_closed.measurable_set] },
    have : (2:ℝ≥0∞) * η = η + η := by simpa using add_mul (1:ℝ≥0∞) 1 η,
    rw this,
    abel },
  -- Apply Urysohn's lemma to get a continuous approximation to the characteristic function of
  -- the set `s`
  obtain ⟨g, hgu, hgF, hg_range⟩ :=
    exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this,
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `u \ F`
  have g_norm : ∀ x, ‖g x‖ = g x := λ x, by rw [real.norm_eq_abs, abs_of_nonneg (hg_range x).1],
  have gc_bd : ∀ x, ‖g x • c - s.indicator (λ x, c) x‖ ≤ ‖(u \ F).indicator (λ x, bit0 ‖c‖) x‖,
  { intros x,
    by_cases hu : x ∈ u,
    { rw ← set.diff_union_of_subset (Fs.trans su) at hu,
      cases hu with hFu hF,
      { refine (norm_sub_le _ _).trans _,
        refine (add_le_add_left (norm_indicator_le_norm_self (λ x, c) x) _).trans _,
        have h₀ : g x * ‖c‖ + ‖c‖ ≤ 2 * ‖c‖,
        { nlinarith [(hg_range x).1, (hg_range x).2, norm_nonneg c] },
        have h₁ : (2:ℝ) * ‖c‖ = bit0 (‖c‖) := by simpa using add_mul (1:ℝ) 1 (‖c‖),
        simp [hFu, norm_smul, h₀, ← h₁, g_norm x] },
      { simp [hgF hF, Fs hF] } },
    { have : x ∉ s := λ h, hu (su h),
      simp [hgu hu, this] } },
  -- The rest is basically just `ennreal`-arithmetic
  have gc_snorm : snorm ((λ x, g x • c) - s.indicator (λ x, c)) p μ
    ≤ (↑(‖bit0 (‖c‖)‖₊ * (2 * η) ^ (1 / p.to_real)) : ℝ≥0∞),
  { refine (snorm_mono_ae (filter.eventually_of_forall gc_bd)).trans _,
    rw snorm_indicator_const (u_open.sdiff F_closed).measurable_set hp₀.ne' hp,
    push_cast [← ennreal.coe_rpow_of_nonneg _ hp₀'],
    exact ennreal.mul_left_mono (ennreal.monotone_rpow_of_nonneg hp₀' h_μ_sdiff) },
  have gc_cont : continuous (λ x, g x • c) := g.continuous.smul continuous_const,
  have gc_mem_ℒp : mem_ℒp (λ x, g x • c) p μ,
  { have : mem_ℒp ((λ x, g x • c) - s.indicator (λ x, c)) p μ :=
    ⟨gc_cont.ae_strongly_measurable.sub (strongly_measurable_const.indicator hs)
        .ae_strongly_measurable,
      gc_snorm.trans_lt ennreal.coe_lt_top⟩,
    simpa using this.add (mem_ℒp_indicator_const p hs c (or.inr hsμ.ne)) },
  refine ⟨gc_mem_ℒp.to_Lp _, _, _⟩,
  { rw mem_closed_ball_iff_norm,
    refine le_trans _ hη_le,
    rw [simple_func.coe_indicator_const, indicator_const_Lp, ← mem_ℒp.to_Lp_sub, Lp.norm_to_Lp],
    exact ennreal.to_real_le_coe_of_le_coe gc_snorm },
  { rw [set_like.mem_coe, mem_bounded_continuous_function_iff],
    refine ⟨bounded_continuous_function.of_normed_add_comm_group _ gc_cont (‖c‖) _, rfl⟩,
    intros x,
    have h₀ : g x * ‖c‖ ≤ ‖c‖,
    { nlinarith [(hg_range x).1, (hg_range x).2, norm_nonneg c] },
    simp [norm_smul, g_norm x, h₀] },
end

end measure_theory.Lp

variables (𝕜 : Type*) [normed_field 𝕜] [normed_algebra ℝ 𝕜] [normed_space 𝕜 E]

namespace bounded_continuous_function
open linear_map (range)

lemma to_Lp_dense_range [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ)).to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp],
end

end bounded_continuous_function

namespace continuous_map
open linear_map (range)

lemma to_Lp_dense_range [compact_space α] [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ)).to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp]
end

end continuous_map
