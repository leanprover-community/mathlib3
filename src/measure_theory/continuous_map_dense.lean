/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import measure_theory.regular
import measure_theory.simple_func_dense
import topology.urysohns_lemma

/-!
# Approximation in Lᵖ by continuous functions

This file defines `measure_theory.Lp.continuous_map E p μ`, the additive subgroup of
`measure_theory.Lp E p μ` consisting of equivalence classes containing a continuous representative.
The main result is `measure_theory.Lp.continuous_map_dense`: for `1 ≤ p < ∞`, if the domain `α` of
the functions is a normal topological space and the measure `μ` is weakly regular, then the
subgroup `Lp.continuous_map E p μ` is dense in `Lp E p μ`.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?  See the
Vitali-Carathéodory theorem, in the file `measure_theory.vitali_caratheodory`.

-/

open_locale ennreal nnreal
open measure_theory topological_space continuous_map

namespace measure_theory.Lp

variables {α : Type*} (E : Type*) [measurable_space α] [topological_space α] [borel_space α]
  [measurable_space E] [normed_group E] [borel_space E] [second_countable_topology E] (p : ℝ≥0∞)
  (μ : measure α)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
continuous representative. -/
def continuous_map : add_subgroup (Lp E p μ) :=
add_monoid_hom.range $
  add_subgroup.inclusion $
    @inf_le_right _ _ (@add_monoid_hom.range C(α, E) _ _ _ (to_ae_eq_fun_add_hom μ)) (Lp E p μ)

variables {E p μ}

/-- By definition, the elements of `Lp.continuous_map E p μ` are the elements of `Lp E p μ` which
contain a continuous representative. -/
lemma mem_continuous_map_iff {f : (Lp E p μ)} :
  f ∈ continuous_map E p μ ↔ ∃ f₀ : C(α, E), to_ae_eq_fun μ f₀ = (f : α →ₘ[μ] E) :=
begin
  split,
  { rintros ⟨⟨f, ⟨⟨f₀, hff₀⟩, hf⟩⟩, rfl⟩,
    exact ⟨f₀, hff₀⟩ },
  { rintros f',
    exact ⟨⟨f, ⟨f', f.2⟩⟩, subtype.ext rfl⟩ }
end

variables [normal_space α] [normed_space ℝ E]

/-- A simple function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma continuous_map_dense [_i : fact (1 ≤ p)] (hp' : p ≠ ∞) [μ.weakly_regular] :
  (continuous_map E p μ).topological_closure = ⊤ :=
begin
  have hp₀ : 0 < p := lt_of_lt_of_le ennreal.zero_lt_one _i.elim,
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one ennreal.to_real_nonneg,
  -- It suffices to prove that scalar multiples of the indicator function of a finite-measure
  -- measurable set can be approximated by continuous functions
  suffices :  ∀ (c : E) {s : set α} (hs : measurable_set s) (hμs : μ s < ⊤),
    (Lp.simple_func.indicator_const p hs hμs.ne c : Lp E p μ)
      ∈ (continuous_map E p μ).topological_closure,
  { rw add_subgroup.eq_top_iff',
    refine Lp.induction hp' _ _ _ _,
    { exact this },
    { exact λ f g hf hg hfg', add_subgroup.add_mem _ },
    { exact add_subgroup.is_closed_topological_closure _ } },
  -- Let `s` be a finite-measure measurable set, let's approximate `c` times its indicator function
  intros c s hs hsμ,
  refine mem_closure_iff_frequently.mpr _,
  rw metric.nhds_basis_closed_ball.frequently_iff,
  intros ε' hε',
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η, (0:ℝ≥0) < η ∧ (↑(∥c∥₊ * (2 * η) ^ (1 / p.to_real)) : ℝ) ≤ ε',
  { sorry },
  have hη_pos' : (0 : ℝ≥0∞) < ↑η := by exact_mod_cast hη_pos,
  -- Use the regularity of the measure to approximate `s` by an open superset and a closed subset
  obtain ⟨u, u_open, su, μu⟩ : ∃ u, is_open u ∧ s ⊆ u ∧ μ u < μ s + ↑η,
  { refine hs.exists_is_open_lt_of_lt _ _,
    simpa using (ennreal.add_lt_add_iff_left hsμ).2 hη_pos' },
  obtain ⟨F, F_closed, Fs, μF⟩ : ∃ F, is_closed F ∧ F ⊆ s ∧ μ s < μ F + ↑η :=
    hs.exists_lt_is_closed_of_lt_top_of_pos hsμ hη_pos',
  have : disjoint uᶜ F,
  { rw [set.disjoint_iff_inter_eq_empty, set.inter_comm, ← set.subset_compl_iff_disjoint],
    simpa using Fs.trans su },
  have h_μ_sdiff : μ (u \ F) ≤ 2 * η,
  { rw ← ennreal.add_lt_add_iff_right (ennreal.coe_lt_top : ↑η < ⊤) at μF,
    have := μu.trans μF,
    sorry },
  -- Apply Urysohn's lemma to get a continuous approximation to the characteristic function of
  -- the set `s`
  obtain ⟨g, hg_cont, hgu, hgF, hg_range⟩ :=
    exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this,
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `u \ F`
  have gc_bd : ∀ x, ∥g x • c - s.indicator (λ x, c) x∥ ≤ ∥(u \ F).indicator (λ x, c) x∥,
  { sorry },
  -- The rest is basically just `ennreal`-arithmetic
  have gc_snorm : snorm ((λ x, g x • c) - s.indicator (λ x, c)) p μ
    ≤ (↑(∥c∥₊ * (2 * η) ^ (1 / p.to_real)) : ℝ≥0∞),
  { refine (snorm_mono_ae (filter.eventually_of_forall gc_bd)).trans _,
    rw snorm_indicator_const (u_open.sdiff F_closed).measurable_set hp₀.ne' hp',
    push_cast [← ennreal.coe_rpow_of_nonneg _ hp₀'],
    exact ennreal.mul_left_mono (ennreal.rpow_left_monotone_of_nonneg hp₀' h_μ_sdiff) },
  have gc_cont : continuous (λ x, g x • c) :=
    continuous_smul.comp (hg_cont.prod_mk continuous_const),
  have gc_mem_ℒp : mem_ℒp (λ x, g x • c) p μ,
  { have : mem_ℒp ((λ x, g x • c) - s.indicator (λ x, c)) p μ :=
    ⟨(gc_cont.ae_measurable μ).sub (measurable_const.indicator hs).ae_measurable,
      gc_snorm.trans_lt ennreal.coe_lt_top⟩,
    simpa using this.add (mem_ℒp_indicator_const p hs c (or.inr hsμ.ne)) },
  refine ⟨gc_mem_ℒp.to_Lp _, _, _⟩,
  { rw mem_closed_ball_iff_norm,
    refine le_trans _ hη_le,
    rw [foo₁, indicator_const_Lp, ← mem_ℒp.to_Lp_sub, Lp.norm_to_Lp],
    exact ennreal.to_real_le_coe_of_le_coe gc_snorm },
  { rw [set_like.mem_coe, mem_continuous_map_iff],
    exact ⟨⟨_, gc_cont⟩, rfl⟩ },

    -- refine hu_ℒp.of_le (hgc_cont.ae_measurable μ) (filter.eventually_of_forall _),
    -- intros a,
    -- by_cases ha : a ∈ uᶜ,
    -- { have : g a = 0 := by simpa using hgu ha,
    --   simp [this] },
    -- { have : ∥g a • c∥ ≤ ∥c∥,
    --   { have : ∥g a∥ = g a := by rw [real.norm_eq_abs, abs_of_nonneg (hg_range a).1],
    --     nlinarith [(hg_range a).2, norm_smul (g a) c, norm_nonneg c] },
    --   have ha' : a ∈ u := by simpa using ha,
    --   simpa [ha'] using this } ,
end

end measure_theory.Lp
