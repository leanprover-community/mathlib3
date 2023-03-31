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
open measure_theory topological_space continuous_map set

variables {α : Type*} [measurable_space α] [topological_space α] [normal_space α] [borel_space α]
variables {E : Type*} [normed_add_comm_group E]

/-- The `L^p` norm of the indicator of a set is uniformly small if the set itself is small.
Given here as an existential `∀ ε > 0, ∃ η > 0` to avoid later management of `ℝ≥0∞`-arithmetic. -/
lemma exists_snorm_indicator_le {α : Type*} {_ : measurable_space α}
  (μ : measure α) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
  ∃ (η : ℝ≥0), 0 < η ∧ ∀ (s : set α), μ s ≤ η → snorm (s.indicator (λ x, c)) p μ ≤ ε :=
begin
  rcases eq_or_ne p 0 with rfl|h'p,
  { exact ⟨1, zero_lt_one, λ s hs, by simp⟩ },
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p,
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one ennreal.to_real_nonneg,
  have hp₀'' : 0 < p.to_real,
  { simpa [← ennreal.to_real_lt_to_real ennreal.zero_ne_top hp] using hp₀ },
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ (η : ℝ≥0), 0 < η ∧ (‖c‖₊ * η ^ (1 / p.to_real) : ℝ≥0∞) ≤ ε,
  { have : filter.tendsto (λ x : ℝ≥0, ((‖c‖₊ * x ^ (1 / p.to_real) : ℝ≥0) : ℝ≥0∞))
      (𝓝 0) (𝓝 (0 : ℝ≥0)),
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
  exact mul_le_mul_left' (ennreal.rpow_le_rpow hs hp₀') _,
end

/-- A variant of Urysohn lemma, `L^p` version for an outer regular measure `μ`:
consider two sets `s ⊆ u` which are respectively closed and open with `μ s < ∞`, and a vector `c`.
Then one may find a continuous function `f` equal to `c` on `s` and to `0` outside of `u`,
bounded by `‖c‖` everywhere, and such that the `L^p` norm of `f - s.indicator (λ y, c)` is
arbitrarily small. Additionally, this function `f` belongs to `L^p`. -/
lemma exists_continuous_snorm_sub_le_of_closed [normed_space ℝ E]
  {s u : set α} (s_closed : is_closed s) (u_open : is_open u) (hsu : s ⊆ u)
  {μ : measure α} [μ.outer_regular] (hs : μ s ≠ ∞) (c : E)
  {p : ℝ≥0∞} (hp : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (f : α → E), continuous f ∧ (∀ x, ‖f x‖ ≤ ‖c‖) ∧ function.support f ⊆ u
    ∧ snorm (λ x, f x - s.indicator (λ y, c) x) p μ ≤ ε ∧ mem_ℒp f p μ :=
begin
  rcases exists_snorm_indicator_le μ c hε hp with ⟨η, η_pos, hη⟩,
  have ηpos : (0 : ℝ≥0∞) < η := ennreal.coe_lt_coe.2 η_pos,
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : set α) (H : V ⊇ s), is_open V ∧ μ V < ∞ ∧ μ (V \ s) < η,
    from s_closed.measurable_set.exists_is_open_diff_lt hs ηpos.ne',
  let v := u ∩ V,
  have v_open : is_open v := u_open.inter V_open,
  have hsv : s ⊆ v := subset_inter hsu sV,
  have hμv : μ v < ∞ := (measure_mono (inter_subset_right _ _)).trans_lt h'V,
  obtain ⟨g, hgv, hgs, hg_range⟩ := exists_continuous_zero_one_of_closed
    v_open.is_closed_compl s_closed (disjoint_compl_left_iff.2 hsv),
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `v \ s`
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
    { have : x ∉ s := λ h, hv (hsv h),
      simp [hgv hv, this], } },
  have gc_support : function.support (λ (x : α), g x • c) ⊆ v,
  { refine function.support_subset_iff'.2 (λ x hx, _),
    simp only [hgv hx, pi.zero_apply, zero_smul] },
  have gc_mem : mem_ℒp (λ x, g x • c) p μ,
  { apply mem_ℒp.smul_of_top_left (mem_ℒp_top_const _),
    refine ⟨g.continuous.ae_strongly_measurable, _⟩,
    have : snorm (v.indicator (λ x, (1 : ℝ))) p μ < ⊤,
    { apply (snorm_indicator_const_le _ _).trans_lt _,
      simp only [lt_top_iff_ne_top, hμv.ne, nnnorm_one, ennreal.coe_one, one_div, one_mul, ne.def,
        ennreal.rpow_eq_top_iff, inv_lt_zero, false_and, or_false, not_and, not_lt,
        ennreal.to_real_nonneg, implies_true_iff] },
    refine lt_of_le_of_lt (snorm_mono (λ x, _)) this,
    by_cases hx : x ∈ v,
    { simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, real.norm_eq_abs,
        indicator_of_mem, cstar_ring.norm_one] },
    { simp only [hgv hx, pi.zero_apply, real.norm_eq_abs, abs_zero, abs_nonneg] } },
  refine ⟨λ x, g x • c, g.continuous.smul continuous_const, gc_bd0,
    gc_support.trans (inter_subset_left _ _), (snorm_mono gc_bd).trans _, gc_mem⟩,
  apply hη,
  exact (measure_mono (diff_subset_diff (inter_subset_right _ _) subset.rfl)).trans hV.le,
end

variables [second_countable_topology_either α E]
  {p : ℝ≥0∞} [_i : fact (1 ≤ p)] (hp : p ≠ ∞) (μ : measure α)

include _i hp

lemma glouk [locally_compact_space α] [normed_space ℝ E] [μ.regular]
  {f : α → E} (hf : mem_ℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α → E), continuous g ∧ mem_ℒp g p μ ∧ has_compact_support g ∧ snorm (f - g) p μ ≤ ε :=
begin
  revert f hf ε ,
  refine mem_ℒp.induction hp _ _ _ _ _,
  { assume c t ht htμ ε hε,
    have h'ε : ε / 2 ≠ 0, sorry,
    rcases exists_snorm_indicator_le μ c h'ε hp with ⟨η, ηpos, hη⟩,
    have hη_pos' : (0 : ℝ≥0∞) < η := ennreal.coe_pos.2 ηpos,
    obtain ⟨s, st, s_compact, μs⟩ : ∃ s ⊆ t, is_compact s ∧ μ (t \ s) < η :=
      ht.exists_is_compact_diff_lt htμ.ne hη_pos'.ne',
    have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ,
    have I1 : snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ ≤ ε/2,
    { rw [← snorm_neg, neg_sub, ← indicator_diff st],
      exact (hη _ μs.le) },
    rcases exists_compact_between s_compact is_open_univ (subset_univ _) with ⟨k, k_compact, sk, -⟩,
    rcases exists_continuous_snorm_sub_le_of_closed s_compact.is_closed is_open_interior sk
      hsμ.ne c hp h'ε with ⟨f, f_cont, f_bound, f_support, I2, f_mem⟩,
    have I3 : snorm (f - t.indicator (λ y, c)) p μ ≤ ε, from calc
      snorm (f - t.indicator (λ y, c)) p μ
        = snorm ((f - s.indicator (λ y, c)) + (s.indicator (λ y, c) - t.indicator (λ y, c))) p μ :
      by simp only [sub_add_sub_cancel]
    ... ≤ snorm (f - s.indicator (λ y, c)) p μ
          + snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ :
      begin
        apply snorm_add_le _ _ _i.out,
        { exact f_mem.ae_strongly_measurable.sub
            (ae_strongly_measurable_const.indicator s_compact.measurable_set) },
        { exact (ae_strongly_measurable_const.indicator s_compact.measurable_set).sub
            (ae_strongly_measurable_const.indicator ht) },
      end
    ... ≤ ε/2 + ε/2 : add_le_add I2 I1
    ... = ε : ennreal.add_halves _,
    refine ⟨f, f_cont, f_mem, _, by rwa [← snorm_neg, neg_sub]⟩,
    apply has_compact_support.intro k_compact (λ x hx, _),

    sorry,
  }

end

#exit

  sorry { assume f f' hff' hf hf' Hf Hf' ε εpos,
    have A : ε / 2 ≠ 0, by simp [εpos],
    rcases Hf A with ⟨g, g_cont, g_mem, hg, hfg⟩,
    rcases Hf' A with ⟨g', g'_cont, g'_mem, hg', hf'g'⟩,
    refine ⟨g + g', g_cont.add g'_cont, g_mem.add g'_mem, hg.add hg', _⟩,
    calc snorm (f + f' - (g + g')) p μ
        = snorm ((f - g) + (f' - g')) p μ : by { congr' 1, abel }
    ... ≤ snorm (f - g) p μ + snorm (f' - g') p μ :
      snorm_add_le (hf.sub g_mem).ae_strongly_measurable
        (hf'.sub g'_mem).ae_strongly_measurable _i.out
    ... ≤ ε / 2 + ε / 2 : add_le_add hfg hf'g'
    ... = ε : ennreal.add_halves _ },
  sorry { rw is_closed_iff_nhds,
    assume f hf ε εpos,
    have A : ε / 2 ≠ 0, by simp [εpos],
    rcases hf (emetric.ball f (ε/2)) (emetric.ball_mem_nhds _ A.bot_lt) with ⟨f', hf', h'f'⟩,
    rcases h'f' A with ⟨g, g_cont, g_mem, g_support, hg⟩,
    refine ⟨g, g_cont, g_mem, g_support, _⟩,
    calc snorm (f - g) p μ = snorm ((f - f') + (f' - g)) p μ : by simp only [sub_add_sub_cancel]
    ... ≤ snorm (f - f') p μ + snorm (f' - g) p μ :
      snorm_add_le ((Lp.mem_ℒp f).sub (Lp.mem_ℒp f')).ae_strongly_measurable
        ((Lp.mem_ℒp f').sub g_mem).ae_strongly_measurable _i.out
    ... ≤ ε / 2 + ε / 2 :
      begin
        refine add_le_add _ hg,
        rw [← snorm_neg, neg_sub],
        simp only [Lp.edist_def, emetric.mem_ball] at hf',
        exact hf'.le
      end
    ... = ε : ennreal.add_halves _ },
  sorry { assume f f' hff' hf Hf ε εpos,
    rcases Hf εpos with ⟨g, g_cont, g_mem, hg, hfg⟩,
    refine ⟨g, g_cont, g_mem, hg, _⟩,
    have : f - g =ᵐ[μ] f' - g := hff'.sub (filter.germ.coe_eq.mp rfl),
    rwa ← snorm_congr_ae this }
end


#exit

variable (E)


namespace measure_theory.Lp

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma bounded_continuous_function_dense [normed_space ℝ E] [μ.weakly_regular] :
  (bounded_continuous_function E p μ).topological_closure = ⊤ :=
begin
  -- It suffices to prove that scalar multiples of the indicator function of a finite-measure
  -- measurable set can be approximated by continuous functions
  suffices :  ∀ (c : E) {s : set α} (hs : measurable_set s) (hμs : μ s < ∞),
    (Lp.simple_func.indicator_const p hs hμs.ne c : Lp E p μ)
      ∈ (bounded_continuous_function E p μ).topological_closure,
  { rw add_subgroup.eq_top_iff',
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
  rcases exists_snorm_indicator_le μ c h'ε hp with ⟨η, ηpos, hη⟩,
  have hη_pos' : (0 : ℝ≥0∞) < η := ennreal.coe_pos.2 ηpos,
  obtain ⟨s, st, s_closed, μs⟩ : ∃ s ⊆ t, is_closed s ∧ μ (t \ s) < η :=
    ht.exists_is_closed_diff_lt htμ.ne hη_pos'.ne',
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ,
  have I1 : snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ ≤ ε'/2,
  { rw [← snorm_neg, neg_sub, ← indicator_diff st],
    exact (hη _ μs.le) },
  rcases exists_continuous_snorm_sub_le_of_closed s_closed is_open_univ (subset_univ _)
    hsμ.ne c hp h'ε with ⟨f, f_cont, f_bound, -, I2, f_mem⟩,
  have I3 : snorm (f - t.indicator (λ y, c)) p μ ≤ ε', from calc
    snorm (f - t.indicator (λ y, c)) p μ
      = snorm ((f - s.indicator (λ y, c)) + (s.indicator (λ y, c) - t.indicator (λ y, c))) p μ :
    by simp only [sub_add_sub_cancel]
  ... ≤ snorm (f - s.indicator (λ y, c)) p μ
        + snorm (s.indicator (λ y, c) - t.indicator (λ y, c)) p μ :
    begin
      apply snorm_add_le _ _ _i.out,
      { exact f_mem.ae_strongly_measurable.sub
          (ae_strongly_measurable_const.indicator s_closed.measurable_set) },
      { exact (ae_strongly_measurable_const.indicator s_closed.measurable_set).sub
          (ae_strongly_measurable_const.indicator ht) },
    end
  ... ≤ ε'/2 + ε'/2 : add_le_add I2 I1
  ... = ε' : ennreal.add_halves _,
  refine ⟨f_mem.to_Lp _, _, _⟩,
  { simp only [dist_eq_norm, simple_func.coe_indicator_const, metric.mem_closed_ball],
    rw [indicator_const_Lp, ← mem_ℒp.to_Lp_sub, Lp.norm_to_Lp],
    apply ennreal.to_real_le_of_le_of_real hε.le,
    convert I3,
    have : ε = ε', by simp only [subtype.coe_mk],
    rw [this, ennreal.of_real_coe_nnreal] },
  { rw [set_like.mem_coe, mem_bounded_continuous_function_iff],
    exact ⟨bounded_continuous_function.of_normed_add_comm_group _ f_cont (‖c‖) f_bound, rfl⟩ },
end

end measure_theory.Lp

variables (𝕜 : Type*) [normed_field 𝕜] [normed_algebra ℝ 𝕜] [normed_space 𝕜 E]

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
