/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv topology.sequences analysis.complex.exponential

/-! # The mean value inequality

A bound on the derivative of a function implies that this function
is Lipschitz continuous for the same bound, on a segment or more generally in a convex set.
This is proved in `norm_image_sub_le_of_norm_deriv_le_convex`.
-/

set_option class.instance_max_depth 120

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set lattice asymptotics continuous_linear_map

/-- The mean value theorem along a segment: a bound on the derivative of a function along a segment
implies a bound on the distance of the endpoints images -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {f : ℝ → F} {C : ℝ}
  (hf : differentiable_on ℝ f (Icc 0 1))
  (bound : ∀t ∈ Icc (0:ℝ) 1, ∥deriv_within f (Icc 0 1) t∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
begin
  /- Let D > C. We will show that, for all t ∈ [0,1], one has ∥f t - f 0∥ ≤ D * t. This is true
  for t=0. Let k be maximal in [0,1] for which this holds. By continuity of all functions, the
  maximum is realized. If k were <1, then a point x slightly to its right would satisfy
  ∥f x - f k∥ ≤ D * (k-x), since the differential of f at k has norm at most C < D. Therefore,
  the point x also satisfies ∥f x - f 0∥ ≤ D * x, contradicting the maximality of k. Hence, k = 1. -/
  refine le_of_forall_le_of_dense (λD hD, _),
  let K := {t ∈ Icc (0 : ℝ) 1 | ∥f t - f 0∥ ≤ D * t},
  let k := Sup K,
  have k_mem_K : k ∈ K,
  { refine cSup_mem_of_is_closed _ _ _,
    show K ≠ ∅,
    { have : (0 : ℝ) ∈ K, by simp [K, le_refl, zero_le_one],
      apply ne_empty_of_mem this },
    show bdd_above K, from ⟨1, λy hy, hy.1.2⟩,
    have A : continuous_on (λt:ℝ, (∥f t - f 0∥, D * t)) (Icc 0 1),
    { apply continuous_on.prod,
      { refine continuous_norm.comp_continuous_on _,
        apply hf.continuous_on.sub continuous_on_const },
      { exact (continuous_const.mul continuous_id).continuous_on } },
    show is_closed K, from
      A.preimage_closed_of_closed is_closed_Icc (ordered_topology.is_closed_le' _) },
  have : k = 1,
  { by_contradiction k_ne_1,
    have k_lt_1 : k < 1 := lt_of_le_of_ne k_mem_K.1.2 k_ne_1,
    have : 0 ≤ k := k_mem_K.1.1,
    let g := deriv_within f (Icc 0 1) k,
    let h := λx, f x - f k - (x-k) • g,
    have : is_o (λ x, h x) (λ x, x - k) (nhds_within k (Icc 0 1)) :=
      (hf k k_mem_K.1).has_deriv_within_at,
    have : {x | ∥h x∥ ≤ (D-C) * ∥x-k∥} ∈ nhds_within k (Icc 0 1) :=
      this (D-C) (sub_pos_of_lt hD),
    rcases mem_nhds_within.1 this with ⟨s, s_open, ks, hs⟩,
    rcases is_open_iff.1 s_open k ks with ⟨ε, εpos, hε⟩,
    change 0 < ε at εpos,
    let δ := min ε (1-k),
    have δpos : 0 < δ, by simp [δ, εpos, k_lt_1],
    let x := k + δ/2,
    have k_lt_x : k < x, by { simp only [x], linarith },
    have x_lt_1 : x < 1 := calc
      x < k + δ : add_lt_add_left (half_lt_self δpos) _
      ... ≤ k + (1-k) : add_le_add_left (min_le_right _ _) _
      ... = 1 : by ring,
    have xε : x ∈ ball k ε,
    { simp [dist, x, abs_of_nonneg (le_of_lt (half_pos δpos))],
      exact lt_of_lt_of_le (half_lt_self δpos) (min_le_left _ _) },
    have xI : x ∈ Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_le_of_lt (k_mem_K.1.1) k_lt_x), le_of_lt x_lt_1⟩,
    have Ih : ∥h x∥ ≤ (D - C) * ∥x - k∥ :=
      hs ⟨hε xε, xI⟩,
    have I : ∥f x - f k∥ ≤ D * (x-k) := calc
      ∥f x - f k∥ = ∥(x-k) • g + h x∥ : by { congr' 1, simp only [h], abel }
      ... ≤ ∥g∥ * ∥x-k∥ + (D-C) * ∥x-k∥ : norm_add_le_of_le (by rw [norm_smul, mul_comm]) Ih
      ... ≤ C * ∥x-k∥ + (D-C) * ∥x-k∥ :
        add_le_add_right (mul_le_mul_of_nonneg_right (bound k k_mem_K.1) (norm_nonneg _)) _
      ... = D * ∥x-k∥ : by ring
      ... = D * (x-k) : by simp [norm, abs_of_nonneg (le_of_lt (half_pos δpos))],
    have : ∥f x - f 0∥ ≤ D * x := calc
      ∥f x - f 0∥ = ∥(f x - f k) + (f k - f 0)∥ : by { congr' 1, abel }
      ... ≤ D * (x - k) + D * k : norm_add_le_of_le I (k_mem_K.2)
      ... = D * x : by ring,
    have xK : x ∈ K := ⟨xI, this⟩,
    have : x ≤ k := le_cSup ⟨1, λy hy, hy.1.2⟩ xK,
    exact (not_le_of_lt k_lt_x) this },
  rw this at k_mem_K,
  simpa [this] using k_mem_K.2
end

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by C, then
the function is C-Lipschitz -/
theorem norm_image_sub_le_of_norm_deriv_le_convex {f : E → F} {C : ℝ} {s : set E} {x y : E}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥fderiv_within ℝ f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
begin
  /- By composition with t ↦ x + t • (y-x), we reduce to a statement for functions defined
  on [0,1], for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
  We just have to check the differentiability of the composition and bounds on its derivative,
  which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_trans (norm_nonneg _) (bound x xs),
  let g := λ(t:ℝ), f (x + t • (y-x)),
  have D1 : differentiable ℝ (λt:ℝ, x + t • (y-x)) :=
    differentiable_const.add (differentiable_id.smul' differentiable_const),
  have segm : (λ (t : ℝ), x + t • (y - x)) '' Icc 0 1 ⊆ s,
    by { rw image_Icc_zero_one_eq_segment, apply (convex_segment_iff _).1 hs x y xs ys },
  have : f x = g 0, by { simp only [g], rw [zero_smul, add_zero] },
  rw this,
  have : f y = g 1, by { simp only [g], rw one_smul, congr' 1, abel },
  rw this,
  apply norm_image_sub_le_of_norm_deriv_le_segment
    (hf.comp D1.differentiable_on (image_subset_iff.1 segm)) (λt ht, _),
  /- It remains to check that the derivative of g is bounded by C ∥y-x∥ at any t ∈ [0,1] -/
  have t_s : x + t • (y-x) ∈ s := segm (mem_image_of_mem _ ht),
  /- Expand the derivative of the composition, and bound its norm by the product of the norms -/
  rw fderiv_within.comp_deriv_within t (hf _ t_s) ((D1 t).differentiable_within_at)
    (image_subset_iff.1 segm) (unique_diff_on_Icc_zero_one t ht),
  refine le_trans (le_op_norm _ _) (mul_le_mul (bound _ t_s) _ (norm_nonneg _) C0),
  have : deriv_within (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t = y - x := calc
    deriv_within (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t
    = deriv (λ (t : ℝ), x + t • (y - x)) t :
      differentiable_at.deriv_within (D1 t) (unique_diff_on_Icc_zero_one t ht)
    ... = deriv (λ (t : ℝ), x) t + deriv (λ (t : ℝ), t • (y-x)) t :
      deriv_add differentiable_at_const ((differentiable_id.smul' differentiable_const) t)
    ... = deriv (λ (t : ℝ), t • (y-x)) t :
      by rw [deriv_const, zero_add]
    ... = t • deriv (λ (t : ℝ), (y-x)) t + (deriv (@_root_.id ℝ) t) • (y - x) :
      deriv_smul' differentiable_at_id differentiable_at_const
    ... = y - x :
      by rw [deriv_const, smul_zero, zero_add, deriv_id, one_smul],
  rw [this]
end


open filter
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
  -- approximate `x` (in the closure of `s`) with a sequence `cx_n` in `s`
  obtain ⟨cx, cxs, cx_lim⟩ : ∃ (cx : ℕ → E), (∀ (n : ℕ), cx n ∈ s) ∧ tendsto cx at_top (𝓝 x) :=
    mem_closure_iff_seq_limit.1 hx,
  have cx_lim' : tendsto cx at_top (nhds_within x s),
  { rw [nhds_within, tendsto_inf, tendsto_principal],
    exact ⟨cx_lim, by simp [cxs]⟩ },
  -- approximate `y` (in the closure of `s`) with a sequence `cy_n` in `s`
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
      exact tendsto_sub ((f_cont y hy.2).tendsto.comp cy_lim') ((f_cont x hx).tendsto.comp cx_lim') },
    have C : tendsto (λn, ε * ∥cy n - cx n∥) at_top (𝓝 (ε * ∥y - x∥)),
    { apply tendsto_mul tendsto_const_nhds (tendsto.comp continuous_norm.continuous_at _),
      apply tendsto_sub cy_lim cx_lim },
    exact le_of_tendsto_of_tendsto (by simp) B C A },
  -- for large `n`, both `cx n` and `cy n` are close to `x`.
  have T₁ : {n | cx n ∈ ball x δ} ∈ at_top :=
    mem_map.1 (cx_lim (ball_mem_nhds x δ_pos)),
  have T₂ : {n | cy n ∈ ball y (δ/2)} ∈ at_top :=
    mem_map.1 (cy_lim (ball_mem_nhds y (half_pos δ_pos))),
  filter_upwards [T₁, T₂],
  assume n hnx hny,
  -- we will apply the mean value inequality to the set `t := s ∩ ball x δ`: it contains `cx n`
  -- and `cy n` when `n` is large, it is convex, and the derivative of `f` is small there by
  -- definition of `δ`.
  let t := s ∩ ball x δ,
  have diff_t : differentiable_on ℝ f t := f_diff.mono (inter_subset_left _ _),
  have t_conv : convex t := convex_inter _ _ s_conv (convex_ball _ _),
  have cxnt : cx n ∈ t := ⟨cxs n, hnx⟩,
  have cynt : cy n ∈ t,
  { refine ⟨cys n, _⟩,
    calc dist (cy n) x ≤ dist (cy n) y + dist y x : dist_triangle _ _ _
    ... < δ/2 + δ/2 : add_lt_add hny hy.1
    ... = δ : by ring },
  refine norm_image_sub_le_of_norm_deriv_le_convex diff_t (λz zt, _) t_conv cxnt cynt,
  have : fderiv_within ℝ f t z = fderiv ℝ f z,
  { have t_open : is_open t := is_open_inter s_open is_open_ball,
    rw differentiable_at.fderiv_within _ (t_open.unique_diff_on z zt),
    apply (diff_t z zt).differentiable_at,
    apply mem_nhds_sets t_open zt },
  rw [this, ← dist_zero_right],
  exact le_of_lt (hδ zt.1 zt.2),
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
    λy hy, tendsto_sub (f_cont y hy) (f'.continuous.comp continuous_id).continuous_within_at,
  have A : ∀y ∈ s, fderiv ℝ f y - f' = fderiv ℝ g y,
  { assume y hy,
    have : has_fderiv_at f (fderiv ℝ f y) y :=
      (differentiable_within_at.differentiable_at (f_diff y hy) (mem_nhds_sets s_open hy)).has_fderiv_at,
    have : has_fderiv_at g (fderiv ℝ f y - f') y :=
      this.sub (f'.has_fderiv_at.comp y (has_fderiv_at_id y)),
    exact this.fderiv.symm },
  have B : tendsto (λy, fderiv ℝ f y - f') (nhds_within x s) (𝓝 (f' - f')) :=
    tendsto_sub h tendsto_const_nhds,
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
  obtain ⟨b, ab, sab⟩ : ∃ (u : ℝ), a < u ∧ Ioc a u ⊆ s :=
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
  obtain ⟨b, ba, sab⟩ : ∃ (l : ℝ), l < a ∧ Ico l a ⊆ s :=
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

namespace partition_unity
open polynomial real
noncomputable theory
open_locale classical

noncomputable def exp_neg_inv_aux_poly : ℕ → polynomial ℝ
| 0 := 1
| (n+1) := X^2 * (exp_neg_inv_aux_poly n).derivative  + (1 - 2 * n * X) * (exp_neg_inv_aux_poly n)

lemma exp_neg_inv_aux_deriv (n : ℕ) (x : ℝ) (hx : 0 < x) :
  has_deriv_at (λx, (exp_neg_inv_aux_poly n).eval x * exp (-1/x) / x^(2 * n)) x
    (λx, (exp_neg_inv_aux_poly n+1).eval x * exp (-1/x) / x^(2 * (n+1))

end partition_unity
