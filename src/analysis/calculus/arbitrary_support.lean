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
open set metric topological_space
open_locale topological_space nnreal

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


theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin
  rcases eq_empty_or_nonempty s with rfl|h's,
  { exact ⟨(λ x, 0), function.support_zero, cont_diff_const,
      by simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩ },
  haveI : nonempty s, from nonempty_coe_sort.mpr h's,
  let u : ℕ → s := dense_seq s,
  have : ∀ n, ∃ (g : E → ℝ), g.support ⊆ s ∧ has_compact_support g ∧ cont_diff ℝ ⊤ g ∧
    range g ⊆ Icc 0 1 ∧ g (u n) = 1,
  { assume n,
    apply exists_smooth_support_subset,
    exact hs.mem_nhds (u n).2 },
  choose g g_supp g_comp_supp g_smooth g_range gu using this,
  obtain ⟨δ, δpos, c, δc⟩ :
    ∃ (δ : ℕ → ℝ≥0), (∀ (i : ℕ), 0 < δ i) ∧ ∃ (c : nnreal), has_sum δ c ∧ c < 1,
    from nnreal.exists_pos_sum_of_countable one_ne_zero ℕ,
  have : ∀ (n : ℕ), ∃ r, 0 < r ∧ ∀ i ≤ n, ∀ x, ∥iterated_fderiv ℝ i (λ x, r * g n x) x∥ ≤ δ n,
  { assume n,
    have : ∃ r, ∀ x, ∥g n x∥ ≤ r,
    { rcases (g_smooth n).continuous.norm.bdd_above_range_of_has_compact_support
        ((g_comp_supp n).comp_left norm_zero) with ⟨r, hr⟩,
      exact ⟨r, λ x, hr (mem_range_self _)⟩ },
    have : ∀ i, ∃ r, ∀ x, ∥iterated_fderiv ℝ i (λ x, g n x) x∥ ≤ r,
    { assume i,
      have A : continuous (iterated_fderiv ℝ i (λ (x : E), g n x)),
        from (g_smooth n).continuous_iterated_fderiv le_top,
      have : bdd_above (range (λ x, ∥iterated_fderiv ℝ i (λ (x : E), g n x) x∥)),
      { apply A.norm.bdd_above_range_of_has_compact_support,
        apply has_compact_support.comp_left _ norm_zero,

      }

    }

  }
end
