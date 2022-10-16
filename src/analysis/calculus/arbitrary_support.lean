/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.specific_functions

/-!
# Arbitrary support

We show that any open set is the support of a smooth function taking values in `[0, 1]`
-/
open set metric topological_space function
open_locale topological_space nnreal

@[to_additive]
lemma continuous.is_open_mul_support {α β : Type*} [topological_space α] [topological_space β]
  [t2_space β] [has_one β]
  {f : α → β} (hf : continuous f) : is_open (mul_support f) :=
is_open_ne_fun hf continuous_const

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

theorem exists_smooth_support_subset {s : set E} {x : E} (hs : s ∈ 𝓝 x) :
  ∃ (f : E → ℝ), f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1 ∧ f x = 1 :=
begin
  obtain ⟨d, d_pos, hd⟩ : ∃ (d : ℝ) (hr : 0 < d), euclidean.ball x d ⊆ s,
    from euclidean.nhds_basis_ball.mem_iff.1 hs,
  let c : cont_diff_bump_of_inner (to_euclidean x) :=
  { r := d/2,
    R := d,
    r_pos := half_pos d_pos,
    r_lt_R := half_lt_self d_pos },
  let f : E → ℝ := c ∘ to_euclidean,
  have f_supp : f.support ⊆ euclidean.ball x d,
  { assume y hy,
    have : to_euclidean y ∈ function.support c,
      by simpa only [f, function.mem_support, function.comp_app, ne.def] using hy,
    rwa c.support_eq at this },
  refine ⟨f, f_supp.trans hd, _, _, _, _⟩,
  { refine is_compact_of_is_closed_bounded is_closed_closure _,
    have : bounded (euclidean.closed_ball x d), from euclidean.is_compact_closed_ball.bounded,
    apply this.mono _,
    refine (is_closed.closure_subset_iff euclidean.is_closed_closed_ball).2 _,
    exact f_supp.trans euclidean.ball_subset_closed_ball },
  { apply c.cont_diff.comp,
    exact continuous_linear_equiv.cont_diff _ },
  { rintros t ⟨y, rfl⟩,
    exact ⟨c.nonneg, c.le_one⟩ },
  { apply c.one_of_mem_closed_ball,
    apply mem_closed_ball_self,
    exact (half_pos d_pos).le }
end


open function
/- is_open_Union_countable [second_countable_topology α]
  {ι} (s : ι → set α) (H : ∀ i, is_open (s i)) :
  ∃ T : set ι, T.countable ∧ (⋃ i ∈ T, s i) = ⋃ i, s i :-/

theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin
  rcases eq_empty_or_nonempty s with rfl|h's,
  sorry { exact ⟨(λ x, 0), function.support_zero, cont_diff_const,
      by simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩ },
  let ι := {f : E → ℝ // f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1},
  obtain ⟨T, T_count, hT⟩ : ∃ T : set ι, T.countable ∧ (⋃ f ∈ T, support (f : E → ℝ)) = s,
  sorry { have : (⋃ (f : ι), (f : E → ℝ).support) = s,
    { refine subset.antisymm (Union_subset (λ f, f.2.1)) _,
      assume x hx,
      rcases exists_smooth_support_subset (hs.mem_nhds hx) with ⟨f, hf⟩,
      let g : ι := ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩,
      have : x ∈ support (g : E → ℝ),
        by simp only [hf.2.2.2.2, subtype.coe_mk, mem_support, ne.def, one_ne_zero, not_false_iff],
      exact mem_Union_of_mem _ this },
    simp_rw ← this,
    apply is_open_Union_countable,
    rintros ⟨f, hf⟩,
    exact hf.2.2.1.continuous.is_open_support },
  obtain ⟨g0, hg⟩ : ∃ (g0 : ℕ → ι), T = range g0,
  sorry { apply countable.exists_eq_range T_count,
    rcases eq_empty_or_nonempty T with rfl|hT,
    { simp only [Union_false, Union_empty] at hT,
      simp only [←hT, not_nonempty_empty] at h's,
      exact h's.elim },
    { exact hT } },
  let g : ℕ → E → ℝ := λ n, (g0 n).1,
  have g_smooth : ∀ n, cont_diff ℝ ⊤ (g n) := λ n, (g0 n).2.2.2.1,
  have g_comp_supp : ∀ n, has_compact_support (g n) := λ n, (g0 n).2.2.1,
  obtain ⟨δ, δpos, c, δc⟩ :
    ∃ (δ : ℕ → ℝ≥0), (∀ (i : ℕ), 0 < δ i) ∧ ∃ (c : nnreal), has_sum δ c ∧ c < 1,
    from nnreal.exists_pos_sum_of_countable one_ne_zero ℕ,
  have : ∀ (n : ℕ), ∃ (r : ℝ),
    0 < r ∧ ∀ i ≤ n, ∀ x, ∥iterated_fderiv ℝ i (r • g n) x∥ ≤ δ n,
  { assume n,
    have : ∀ i, ∃ R, ∀ x, ∥iterated_fderiv ℝ i (λ x, g n x) x∥ ≤ R,
    { assume i,
      have : bdd_above (range (λ x, ∥iterated_fderiv ℝ i (λ (x : E), g n x) x∥)),
      { apply ((g_smooth n).continuous_iterated_fderiv le_top).norm
          .bdd_above_range_of_has_compact_support,
        apply has_compact_support.comp_left _ norm_zero,
        apply (g_comp_supp n).iterated_fderiv },
      rcases this with ⟨R, hR⟩,
      exact ⟨R, λ x, hR (mem_range_self _)⟩ },
    choose R hR using this,
    let M := max (((finset.range (n+1)).image R).max' (by simp)) 1,
    have M_pos : 0 < M := zero_lt_one.trans_le (le_max_right _ _),
    have δnpos : 0 < δ n := δpos n,
    have : ∀ i ≤ n, R i ≤ M,
    { assume i hi,
      refine le_trans _ (le_max_left _ _),
      apply finset.le_max',
      apply finset.mem_image_of_mem,
      simp only [finset.mem_range],
      linarith },
    refine ⟨M⁻¹ * δ n, by positivity, λ i hi x, _⟩,
    rw iterated_fderiv_const_smul_apply,
    swap, { exact (g_smooth n).of_le le_top },
    calc ∥(M⁻¹ * ↑(δ n)) • iterated_fderiv ℝ i (g n) x∥
        = M⁻¹ * δ n * ∥iterated_fderiv ℝ i (g n) x∥ : sorry
    ... ≤ M⁻¹ * δ n * M : sorry
    ... = δ n : by field_simp [M_pos.ne'] }
end
