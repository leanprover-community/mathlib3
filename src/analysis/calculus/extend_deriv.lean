/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.mean_value topology.sequences

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/

set_option class.instance_max_depth 40

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open filter set metric continuous_linear_map
open_locale topological_space

/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to `0` at a point on the boundary, then `f` is differentiable there with
derivative `0`. This is an auxiliary statement to prove the same result for any value of the
derivative, in `has_fderiv_at_boundary_of_tendsto_fderiv`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv_aux {f : E → F} {s : set E} {x : E}
  (f_diff : differentiable_on ℝ f s) (s_conv : convex s) (s_open : is_open s)
  (f_cont : ∀y ∈ closure s, continuous_within_at f s y)
  (h : tendsto (λy, fderiv ℝ f y) (nhds_within x s) (𝓝 0)) :
  has_fderiv_within_at f (0 : E →L[ℝ] F) (closure s) x :=
begin
  classical,
  -- one can assume without loss of generality that `x` belongs to the closure of `s`, as the
  -- statement is empty otherwise
  by_cases hx : x ∉ closure s,
  { rw ← closure_closure at hx, exact has_fderiv_within_at_of_not_mem_closure hx },
  replace hx : x ∈ closure s, by simpa using hx,
  /- One needs to show that `∥f y - f x∥ ≤ ε ∥y - x∥` for `y` close to `x` in `closure s`, where
  `ε` is an arbitrary positive constant. By continuity of the functions, it suffices to prove this
  for nearby points inside `s`. In a neighborhood of `x`, the derivative of `f` is arbitrarily small
  by assumption. The mean value inequality ensures that `f` is `ε`-Lipschitz there, concluding the
  proof. -/
  assume ε ε_pos,
  obtain ⟨δ, δ_pos, hδ⟩ : ∃δ>0, ∀ y ∈ s, dist y x < δ → dist (fderiv ℝ f y) 0 < ε :=
    tendsto_nhds_within_nhds.1 h ε ε_pos,
  refine mem_nhds_within_iff.2 ⟨δ/2, half_pos δ_pos, λy hy, _⟩,
  suffices : ∥f y - f x∥ ≤ ε * ∥y - x∥, by simpa,
  -- approximate `x` (in the closure of `s`) with a sequence `cx n` in `s`
  obtain ⟨cx, cxs, cx_lim⟩ : ∃ (cx : ℕ → E), (∀ (n : ℕ), cx n ∈ s) ∧ tendsto cx at_top (𝓝 x) :=
    mem_closure_iff_seq_limit.1 hx,
  have cx_lim' : tendsto cx at_top (nhds_within x s),
  { rw [nhds_within, tendsto_inf, tendsto_principal],
    exact ⟨cx_lim, by simp [cxs]⟩ },
  -- approximate `y` (in the closure of `s`) with a sequence `cy n` in `s`
  obtain ⟨cy, cys, cy_lim⟩ : ∃ (cy : ℕ → E), (∀ (n : ℕ), cy n ∈ s) ∧ tendsto cy at_top (𝓝 y) :=
    mem_closure_iff_seq_limit.1 hy.2,
  have cy_lim' : tendsto cy at_top (nhds_within y s),
  { rw [nhds_within, tendsto_inf, tendsto_principal],
    exact ⟨cy_lim, by simp [cys]⟩ },
  -- by continuity, it suffices to show that `∥f (cy n) - f (cx n)∥ ≤ ε * ∥(cy n) - (cx n)∥` for
  -- large `n`, and then pass to the limit in `n`.
  suffices A : {n | ∥f (cy n) - f (cx n)∥ ≤ ε * ∥(cy n) - (cx n)∥} ∈ at_top,
  { have B : tendsto (λn, ∥f (cy n) - f (cx n)∥) at_top (𝓝 (∥f y - f x∥)),
    { apply tendsto.comp continuous_norm.continuous_at,
      exact ((f_cont y hy.2).tendsto.comp cy_lim').sub ((f_cont x hx).tendsto.comp cx_lim') },
    have C : tendsto (λn, ε * ∥cy n - cx n∥) at_top (𝓝 (ε * ∥y - x∥)) :=
      tendsto_const_nhds.mul (tendsto.comp continuous_norm.continuous_at (cy_lim.sub cx_lim)),
    exact le_of_tendsto_of_tendsto (by simp) B C A },
  -- for large `n`, both `cx n` and `cy n` are close to `x`.
  have T₁ : {n | cx n ∈ ball x δ} ∈ at_top :=
    mem_map.1 (cx_lim (ball_mem_nhds x δ_pos)),
  have T₂ : {n | cy n ∈ ball y (δ/2)} ∈ at_top :=
    mem_map.1 (cy_lim (ball_mem_nhds y (half_pos δ_pos))),
  filter_upwards [T₁, T₂],
  assume n hnx hny,
  /- we will apply the mean value inequality to the set `t := s ∩ ball x δ`: it contains `cx n`
     and `cy n` when `n` is large, it is convex, and the derivative of `f` is small there by
     definition of `δ`. -/
  let t := s ∩ ball x δ,
  have diff_t : differentiable_on ℝ f t := f_diff.mono (inter_subset_left _ _),
  have t_conv : convex t := s_conv.inter (convex_ball _ _),
  have cxnt : cx n ∈ t := ⟨cxs n, hnx⟩,
  have cynt : cy n ∈ t,
  { refine ⟨cys n, _⟩,
    calc dist (cy n) x ≤ dist (cy n) y + dist y x : dist_triangle _ _ _
    ... < δ/2 + δ/2 : add_lt_add hny hy.1
    ... = δ : by ring },
  refine t_conv.norm_image_sub_le_of_norm_deriv_le diff_t (λz zt, _) cxnt cynt,
  have : fderiv_within ℝ f t z = fderiv ℝ f z,
  { have t_open : is_open t := is_open_inter s_open is_open_ball,
    rw differentiable_at.fderiv_within _ (t_open.unique_diff_on z zt),
    apply (diff_t z zt).differentiable_at,
    apply mem_nhds_sets t_open zt },
  rw [this, ← dist_zero_right],
  exact le_of_lt (hδ zt.1 zt.2)
end

/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv {f : E → F} {s : set E} {x : E} {f' : E →L[ℝ] F}
  (f_diff : differentiable_on ℝ f s) (s_conv : convex s) (s_open : is_open s)
  (f_cont : ∀y ∈ closure s, continuous_within_at f s y)
  (h : tendsto (λy, fderiv ℝ f y) (nhds_within x s) (𝓝 f')) :
  has_fderiv_within_at f f' (closure s) x :=
begin
  /- We subtract `f'` to define a new function `g` for which `g' = 0`, for which differentiability
  is proved `has_fderiv_at_boundary_of_differentiable_aux`. Then, we just need to glue together the
  pieces, expressing back `f` in terms of `g`. -/
  let g := λy, f y - f' y,
  have diff_g : differentiable_on ℝ g s :=
    f_diff.sub (f'.differentiable.comp differentiable_id).differentiable_on,
  have cont_g : ∀y ∈ closure s, continuous_within_at g s y :=
    λy hy, tendsto.sub (f_cont y hy) (f'.continuous.comp continuous_id).continuous_within_at,
  have A : ∀y ∈ s, fderiv ℝ f y - f' = fderiv ℝ g y,
  { assume y hy,
    have : has_fderiv_at f (fderiv ℝ f y) y :=
      (differentiable_within_at.differentiable_at (f_diff y hy) (mem_nhds_sets s_open hy)).has_fderiv_at,
    have : has_fderiv_at g (fderiv ℝ f y - f') y :=
      this.sub (f'.has_fderiv_at.comp y (has_fderiv_at_id y)),
    exact this.fderiv.symm },
  have B : tendsto (λy, fderiv ℝ f y - f') (nhds_within x s) (𝓝 (f' - f')) :=
    h.sub tendsto_const_nhds,
  have : tendsto (λy, fderiv ℝ g y) (nhds_within x s) (𝓝 0),
  { have : f' - f' = 0, by simp,
    rw this at B,
    apply tendsto.congr' _ B,
    filter_upwards [self_mem_nhds_within] A },
  have : has_fderiv_within_at g (0 : E →L[ℝ] F) (closure s) x :=
    has_fderiv_at_boundary_of_tendsto_fderiv_aux diff_g s_conv s_open cont_g this,
  convert this.add f'.has_fderiv_within_at,
  { ext y, simp [g] },
  { simp }
end

/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
lemma has_deriv_at_interval_left_endpoint_of_tendsto_deriv {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : differentiable_on ℝ f s) (f_lim : continuous_within_at f s a)
  (hs : s ∈ nhds_within a (Ioi a))
  (f_lim' : tendsto (λx, deriv f x) (nhds_within a (Ioi a)) (𝓝 e)) :
  has_deriv_within_at f e (Ici a) a :=
begin
  /- This is a specialization of `has_fderiv_at_boundary_of_tendsto_fderiv`. To be in the setting of
  this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
  call `t = (a, b)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ab, sab⟩ : ∃ b ∈ Ioi a, Ioc a b ⊆ s :=
    mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hs,
  let t := Ioo a b,
  have ts : t ⊆ s := subset.trans Ioo_subset_Ioc_self sab,
  have t_diff : differentiable_on ℝ f t := f_diff.mono ts,
  have t_conv : convex t := convex_Ioo a b,
  have t_open : is_open t := is_open_Ioo,
  have t_closure : closure t = Icc a b := closure_Ioo ab,
  have t_cont : ∀y ∈ closure t, continuous_within_at f t y,
  { rw t_closure,
    assume y hy,
    by_cases h : y = a,
    { rw h, exact f_lim.mono ts },
    { have : y ∈ s := sab ⟨lt_of_le_of_ne hy.1 (ne.symm h), hy.2⟩,
      exact (f_diff.continuous_on y this).mono ts } },
  have t_diff' : tendsto (λx, fderiv ℝ f x) (nhds_within a t) (𝓝 (smul_right 1 e)),
  { simp [deriv_fderiv.symm],
    refine tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _,
    exact tendsto_le_left (nhds_within_mono _ Ioo_subset_Ioi_self) f_lim' },
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : has_deriv_within_at f e (Icc a b) a,
  { rw [has_deriv_within_at_iff_has_fderiv_within_at, ← t_closure],
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' },
  exact this.nhds_within (mem_nhds_within_Ici_iff_exists_Icc_subset.2 ⟨b, ab, subset.refl _⟩)
end

/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
lemma has_fderiv_at_interval_right_endpoint_of_tendsto_deriv {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : differentiable_on ℝ f s) (f_lim : continuous_within_at f s a)
  (hs : s ∈ nhds_within a (Iio a))
  (f_lim' : tendsto (λx, deriv f x) (nhds_within a (Iio a)) (𝓝 e)) :
  has_deriv_within_at f e (Iic a) a :=
begin
  /- This is a specialization of `has_fderiv_at_boundary_of_differentiable`. To be in the setting of
  this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
  call `t = (b, a)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ba, sab⟩ : ∃ (b : ℝ), b < a ∧ Ico b a ⊆ s :=
    mem_nhds_within_Iio_iff_exists_Ico_subset.1 hs,
  let t := Ioo b a,
  have ts : t ⊆ s := subset.trans Ioo_subset_Ico_self sab,
  have t_diff : differentiable_on ℝ f t := f_diff.mono ts,
  have t_conv : convex t := convex_Ioo b a,
  have t_open : is_open t := is_open_Ioo,
  have t_closure : closure t = Icc b a := closure_Ioo ba,
  have t_cont : ∀y ∈ closure t, continuous_within_at f t y,
  { rw t_closure,
    assume y hy,
    by_cases h : y = a,
    { rw h, exact f_lim.mono ts },
    { have : y ∈ s := sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩,
      exact (f_diff.continuous_on y this).mono ts } },
  have t_diff' : tendsto (λx, fderiv ℝ f x) (nhds_within a t) (𝓝 (smul_right 1 e)),
  { simp [deriv_fderiv.symm],
    refine tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _,
    exact tendsto_le_left (nhds_within_mono _ Ioo_subset_Iio_self) f_lim' },
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : has_deriv_within_at f e (Icc b a) a,
  { rw [has_deriv_within_at_iff_has_fderiv_within_at, ← t_closure],
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' },
  exact this.nhds_within (mem_nhds_within_Iic_iff_exists_Icc_subset.2 ⟨b, ba, subset.refl _⟩)
end
