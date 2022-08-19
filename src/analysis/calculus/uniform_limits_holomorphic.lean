/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import analysis.complex.cauchy_integral
import analysis.calculus.fderiv_analytic
import analysis.calculus.uniform_limits_deriv
import topology.uniform_space.complete_separated

/-!
# Uniform limits of holomorphic functions are holomorphic

The purpose of this file is to prove that a uniform limit of holomorphic functions is holomorphic,
a critical component of many theories, notably that of Dirichlet series.

## Definitions

* `formal_multilinear_series.antideriv` : The formal antiderivative of a power series with a one
  dimensional domain
* `has_fpower_series_on_ball.antideriv` : The formal antiderivative of an analytic function on a
  ball

## Main statements

* `has_fpower_series_on_ball.antideriv_has_deriv_at` : Morera's Theorem. A function on `ℝ` or `ℂ`
  that is analytic on a ball admits an antiderivative on that ball.
* `complex.analytic_at_of_tendsto_uniformly_on` : If `f : ℕ → ℂ → ℂ` is a sequence functions which
  are analytic on a shared neighborhood of `x` and they converge _uniformly_ to `g : ℂ → ℂ` on that
  neighborhood, then `f` is also analytic at `x`.
* `complex.analytic_on_of_tendsto_uniformly_on` : Same as above, but if the shared neighborhood `s`
  is _open_, then in fact `f` is analytic on all of `s`.


## Implementation notes

The steps to our proof are:
  * Develop a language which lets us translate between the vast complexity of formal multilinear
    series that form the foundation of analyticity in mathlib, and more prosaic sums when we're in
    one dimension
  * Given an analytic function `f : 𝕜 → 𝕜` on _any_ nontrivially normed field, define an
    antiderivative `F : 𝕜 → 𝕜`
  * Now when `𝕜` is either `ℝ` or `ℂ`, use the mean value theorem to show that given a sequence of
    analytic functions `f : ℕ → 𝕜 → 𝕜`, the sequence of antiderivatives `F : ℕ → 𝕜 → 𝕜` form a
    uniform Cauchy sequence and thus converge to some function `G`
  * Apply `has_fderiv_at_of_tendsto_uniformly_on` to show that `G' = g` and so, when
    `𝕜 = ℂ`, we have that `G` is analytic (`differentiable_on.analytic_on`) and thus so is `g`
    (`analytic_on.fderiv`)

## Tags

uniform convergence, holomorphic functions, morera's theorem
-/

open filter nat
open_locale big_operators topological_space uniformity

variables {ι 𝕜 E F : Type*} [fintype ι] [decidable_eq ι]

section general

@[simp] lemma norm_const_zero {ι M : Type*} [fintype ι] [nonempty ι] [normed_add_comm_group M] :
  ∥(0 : ι → M)∥ = 0 :=
by { convert pi_norm_const (0 : M), rw norm_zero, apply_instance }

@[simp] lemma norm_const_one {ι M : Type*} [fintype ι] [nonempty ι] [has_one M]
  [normed_add_comm_group M] [norm_one_class M] :
  ∥(1 : ι → M)∥ = 1 :=
by { convert pi_norm_const (1 : M), rw norm_one, apply_instance }

@[simp] lemma norm_is_empty {ι M : Type*} [is_empty ι] [normed_add_comm_group M] (f : ι → M) :
  ∥f∥ = 0 :=
by { rw subsingleton.elim f 0, refl }

lemma foo₁ [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] (f : multilinear_map 𝕜 (λ i : ι, 𝕜) E)
  (x : ι → 𝕜) : f x = (∏ i, x i) • (f 1) :=
begin
  rw ← multilinear_map.map_smul_univ,
  exact congr_arg f (funext $ λ i, by simp)
end

lemma bar₁ [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space 𝕜] [topological_space E]
  (f : continuous_multilinear_map 𝕜 (λ i : ι, 𝕜) E)
  (x : ι → 𝕜) : f x = (∏ i, x i) • (f 1) :=
foo₁ f.to_multilinear_map x

lemma partial_sum₁ [comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [topological_space E] [topological_add_group E] [has_continuous_const_smul 𝕜 E]
  (φ : formal_multilinear_series 𝕜 𝕜 E) (x : 𝕜) (n : ℕ) :
  φ.partial_sum n x = ∑ k in finset.range n, x^k • (φ k 1) :=
begin
  rw formal_multilinear_series.partial_sum,
  congr,
  ext n,
  rw [bar₁, fin.prod_const],
end

lemma partial_sum5 [comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [topological_space E] [topological_add_group E] [has_continuous_const_smul 𝕜 E]
  (φ : formal_multilinear_series 𝕜 𝕜 E) (n : ℕ) :
  φ.partial_sum n = (λ x : 𝕜, ∑ k in finset.range n, x^k • (φ k 1)) :=
begin
  ext,
  exact partial_sum₁ φ x n,
end

end general

section normed_field
variables [normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

/-- The formal antiderivative of a multilinear power series with a one-dimensional domain. Note
that while we have defined this for any `normed_field`, it really only makes sense when that
field is characterisitic 0. -/
def formal_multilinear_series.antideriv (φ : formal_multilinear_series 𝕜 𝕜 E) :
  formal_multilinear_series 𝕜 𝕜 E
| 0 := 0
| (n + 1) := ((n + 1) : 𝕜)⁻¹ •
  (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 (n + 1) 𝕜).smul_right (φ n 1)

end normed_field

section nontrivially_normed_field

variables [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

lemma continuous_multilinear_map.norm_one_dim {f : continuous_multilinear_map 𝕜 (λ i : ι, 𝕜) E} :
  ∥f∥ = ∥f 1∥ :=
begin
  refine le_antisymm _ _,
  convert continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) _,
  { intros m,
    apply le_of_eq,
    have : f m = (∏ i, m i) • (f 1),
    { convert bar₁ _ m, },
    rw [this, norm_smul, mul_comm, norm_prod], },

  { convert continuous_multilinear_map.unit_le_op_norm _ 1 _,
    refl,
    casesI is_empty_or_nonempty ι,
    { refine le_of_eq_of_le _ zero_le_one,
      simp only [norm_eq_zero, eq_iff_true_of_subsingleton], },
    { exact norm_const_one.le, }, },
end

lemma continuous_multilinear_map.norm_smul_right {f : continuous_multilinear_map 𝕜 (λ i : ι, 𝕜) 𝕜}
  {x : E} : ∥f.smul_right x∥ = ∥f∥ * ∥x∥ :=
by rw [continuous_multilinear_map.norm_one_dim, continuous_multilinear_map.norm_one_dim,
  continuous_multilinear_map.smul_right_apply, norm_smul]

end nontrivially_normed_field

section is_R_or_C

variables [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
  (φ : formal_multilinear_series 𝕜 𝕜 E)

lemma formal_multilinear_series.antideriv_radius_mono_aux {r : nnreal}
  (hr : ↑r < φ.radius) : ↑r ≤ φ.antideriv.radius :=
begin
  obtain ⟨C, hC, hm⟩ := φ.norm_mul_pow_le_of_lt_radius hr,
  refine formal_multilinear_series.le_radius_of_bound _ (C * r) _,
  intros n,
  induction n with n hn,
  { simp only [formal_multilinear_series.antideriv, norm_zero, zero_mul],
    exact mul_nonneg hC.lt.le nnreal.zero_le_coe, },

  have : n.succ = n + 1, refl,
  rw this,
  dunfold formal_multilinear_series.antideriv,
  rw [norm_smul, continuous_multilinear_map.norm_smul_right, norm_inv,
    continuous_multilinear_map.norm_mk_pi_algebra_fin, one_mul, pow_add (r : ℝ) n 1,
    ← mul_assoc, pow_one, ← continuous_multilinear_map.norm_one_dim],

  refine mul_le_mul _ rfl.le nnreal.zero_le_coe hC.lt.le,
  have : C = 1 * C, simp,
  rw [this, mul_assoc],
  refine mul_le_mul _ (hm n)
    (mul_nonneg (norm_nonneg _) (by simp only [pow_nonneg, nnreal.zero_le_coe])) zero_le_one,

  norm_cast,
  rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat],
  rw inv_le _ zero_lt_one,
  { simp, },
  { norm_cast, simp, },
  { apply_instance, },
end

lemma formal_multilinear_series.antideriv_radius_mono :
  φ.radius ≤ φ.antideriv.radius :=
begin
  by_contradiction h,
  push_neg at h,
  obtain ⟨r, hr, hr'⟩ := ennreal.lt_iff_exists_nnreal_btwn.mp h,
  exact not_lt_of_le rfl.le
    (lt_of_lt_of_le hr (φ.antideriv_radius_mono_aux hr')),
end

lemma formal_multilinear_series.antideriv_has_deriv_at_parial_sum {y : 𝕜} {n : ℕ} :
  has_deriv_at (φ.antideriv.partial_sum n.succ) (φ.partial_sum n y) y :=
begin
  -- Proof is by induction and the fact that d/dx (x^n) = n x^(n - 1)
  rw partial_sum₁,
  rw partial_sum5,
  induction n with n hn,
  { -- base case is trivial as it's an empty sum
    simp only [finset.range_one, finset.sum_singleton, pow_zero, one_smul,
    finset.range_zero, finset.sum_empty],
    exact has_deriv_at_const y _, },

  -- Inductive case's main difficulty is cancelling (n + 1)⁻¹ through a bunch of casts
  rw finset.sum_range_succ,
  conv { congr, funext, rw finset.sum_range_succ, },
  refine has_deriv_at.add hn _,
  simp only [formal_multilinear_series.antideriv, continuous_multilinear_map.smul_apply,
    continuous_multilinear_map.smul_right_apply, continuous_multilinear_map.mk_pi_algebra_fin_apply,
    list.of_fn_succ, pi.one_apply, list.of_fn_const, list.prod_cons, list.prod_repeat, one_pow,
    mul_one, one_smul],
  conv { congr, funext, rw ← smul_assoc, },
  refine has_deriv_at.smul_const _ (φ n 1),
  have aa := (has_deriv_at_pow (n + 1) y).const_mul ((n : 𝕜) + 1)⁻¹,
  simp only [cast_add, cast_one, add_succ_sub_one, add_zero] at aa,
  have : (((n : 𝕜) + 1)⁻¹ * (((n : 𝕜) + 1) * y ^ n)) = y ^ n,
  { rw ←mul_assoc,
    conv { congr, skip, rw ← one_mul (y ^ n), },
    congr,
    rw inv_mul_cancel,
    norm_cast,
    simp, },
  rw this at aa,
  apply aa.congr_of_eventually_eq,
  simp only [eventually_eq, algebra.id.smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero],
  exact eventually_of_forall (λ y, by rw mul_comm),
end

lemma formal_multilinear_series.antideriv_has_deriv_at_sum [complete_space E] {y : 𝕜}
  (hφ : 0 < φ.radius) (hy' : y ∈ emetric.ball (0 : 𝕜) φ.radius) :
  has_deriv_at φ.antideriv.sum (φ.sum y) y :=
begin
  -- For technical reasons involving uniform convergence, we need to shrink our radius
  obtain ⟨r, hr, hr'⟩ : ∃ (r : nnreal), nndist y 0 < r ∧ ↑r < φ.radius,
  { suffices : ∃ (r : nnreal), ((nndist y 0) : ennreal) < r ∧ ↑r < φ.radius,
    { obtain ⟨r, hr, hr'⟩ := this,
      refine ⟨r, (by simpa using hr), hr'⟩, },
    rw [emetric.mem_ball, edist_nndist] at hy',
    exact ennreal.lt_iff_exists_nnreal_btwn.mp hy', },

  -- Ultimately, we'll use the fact that you can swap limits and derivatives when
  -- the derivatives converge uniformly
  have h3 : ∀ z : 𝕜, z ∈ metric.ball (0 : 𝕜) r →
    tendsto (λ n : ℕ, φ.antideriv.partial_sum n.succ z) at_top (𝓝 (φ.antideriv.sum z)),
    { intros z hz,
      suffices ha : tendsto (λ (n : ℕ), φ.antideriv.partial_sum n z) at_top
        (𝓝 (φ.antideriv.sum z)),
      { exact ha.comp
        (tendsto_at_top_at_top_of_monotone (λ b c, succ_le_succ) (λ b, ⟨b, le_succ b⟩)), },
      have h1 := lt_of_lt_of_le hφ φ.antideriv_radius_mono,
      have h2 := lt_of_lt_of_le hr' φ.antideriv_radius_mono,
      have h3 := ((φ.antideriv.has_fpower_series_on_ball h1).tendsto_uniformly_on h2).tendsto_at hz,
      simpa using h3, },

  refine has_deriv_at_of_tendsto_uniformly_on metric.is_open_ball _ h3
    (by simpa using (φ.has_fpower_series_on_ball hφ).tendsto_uniformly_on hr') y hr,
  { intros n z hz, exact φ.antideriv_has_deriv_at_parial_sum, },
end

end is_R_or_C

section is_R_or_C_fpower_series
variables [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E] [complete_space E]
  {f : 𝕜 → E} {φ : formal_multilinear_series 𝕜 𝕜 E} {x : 𝕜} {r : ennreal}

/-- The antiderivative of an analytic funciton -/
noncomputable def has_fpower_series_on_ball.antideriv
  (h : has_fpower_series_on_ball f φ x r) : 𝕜 → E :=
λ z, φ.antideriv.sum (z - x)

lemma has_fpower_series_on_ball.antideriv_has_fpower_series_on_ball
  (h : has_fpower_series_on_ball f φ x r) :
  has_fpower_series_on_ball h.antideriv φ.antideriv x r :=
begin
  have : x = 0 + x, simp,
  conv {congr, skip, skip, rw this,},
  dunfold has_fpower_series_on_ball.antideriv,
  apply has_fpower_series_on_ball.comp_sub,
  refine has_fpower_series_on_ball.mono _ h.r_pos (h.r_le.trans φ.antideriv_radius_mono),
  refine φ.antideriv.has_fpower_series_on_ball _,
  calc 0 < r : h.r_pos
    ... ≤ φ.radius : h.r_le
    ... ≤ φ.antideriv.radius : φ.antideriv_radius_mono,
end

/-- **Morera's Theorem**: An analytic function over `ℝ` or `ℂ` admits an antiderivative -/
lemma has_fpower_series_on_ball.antideriv_has_deriv_at
  (h : has_fpower_series_on_ball f φ x r) {y : 𝕜} (hy : y ∈ emetric.ball x r) :
  has_deriv_at h.antideriv (f y) y :=
begin
  let recenter : 𝕜 → 𝕜 := (λ z, z - x),
  have : h.antideriv = φ.antideriv.sum ∘ recenter,
  { funext,
    simp [has_fpower_series_on_ball.antideriv, formal_multilinear_series.antideriv, recenter], },
  rw this,
  have hyr : y - x ∈ emetric.ball (0 : 𝕜) r,
  { rw [emetric.mem_ball, edist_dist, dist_eq_norm] at hy ⊢,
    rw sub_zero,
    exact hy, },
  have hyφ : y - x ∈ emetric.ball (0 : 𝕜) φ.radius,
  { exact set.mem_of_mem_of_subset hyr (emetric.ball_subset_ball h.r_le), },
  have := φ.antideriv_has_deriv_at_sum (lt_of_lt_of_le h.r_pos h.r_le) hyφ,
  have aa := has_deriv_at.scomp y this ((has_deriv_at_id y).sub_const x),
  have bb : f y = φ.sum (y - x), { simpa using h.sum hyr, },
  rw ←bb at aa,
  simpa using aa,
end

/-- **Morera's Theorem**: An analytic function over `ℝ` or `ℂ` admits an antiderivative -/
lemma has_fpower_series_at.antideriv_has_deriv_at
  (h : has_fpower_series_at f φ x) :
  has_deriv_at (classical.some_spec h).antideriv (f x) x :=
begin
  refine has_fpower_series_on_ball.antideriv_has_deriv_at _ _,
  rw [emetric.mem_ball, edist_self],
  exact (classical.some_spec h).r_pos,
end

end is_R_or_C_fpower_series

section complex
variables {η : Type*} {l : filter η} [ne_bot l]
  [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {f : η → ℂ → E} {g : ℂ → E} {φ : formal_multilinear_series ℂ ℂ E} {x : ℂ}
  {r : ennreal} {s : set ℂ}

/-- If a sequence of holomorphic functions converges uniformly on a neighborhhod of `x`, then the
limit is also holomorphic at `x`. -/
theorem complex.analytic_at_of_tendsto_uniformly_on (hs : s ∈ 𝓝 x)
  (hf : ∀ (n : η), analytic_on ℂ (f n) s)
  (hfg : tendsto_uniformly_on f g l s) : analytic_at ℂ g x :=
begin
  -- Proof strategy: We will use the fact that the complex derivative of a complex function is
  -- analytic. To do so, we first construct antiderivatives of `f n` and `g` by shrinking to a
  -- small ball around `x` and applying the above machinery
  obtain ⟨_r, h_r, h_r'⟩ := metric.nhds_basis_closed_ball.mem_iff.mp hs,
  let r : nnreal := _r.to_nnreal,
  have hr : 0 < r, exact real.to_nnreal_pos.mpr h_r,
  have : max _r 0 = _r, { exact max_eq_left_of_lt h_r, },
  have hr' : metric.closed_ball x r ⊆ s, {simp [this, h_r'], },

  -- Our first use of `ℂ` instead of `ℝ`: An analytic function has a power series which converges on
  -- the largest ball on which the function is differentiable. We use this to get a _common_ radius
  -- of convergence.
  have hfp : ∀ n, has_fpower_series_on_ball (f n) (cauchy_power_series (f n) x r) x r,
  { intros n,
    refine differentiable_on.has_fpower_series_on_ball _ hr,
    intros y hy,
    exact (hf n y (set.mem_of_mem_of_subset hy hr')).differentiable_at.differentiable_within_at, },

  -- Construct the antiderivatives
  let F : η → ℂ → E := (λ n, (hfp n).antideriv),
  let G : ℂ → E := (λ z, lim l (λ n, F n z)),

  -- Show that the `F` converge (necessarily to `G`) via
  -- `uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_deriv`
  have hF : ∀ n y, y ∈ metric.ball x r → has_deriv_at (F n) (f n y) y,
  { intros n y hy,
    have : y ∈ emetric.ball x r,
    { rw [emetric.mem_ball, edist_nndist],
      rw [metric.mem_ball, dist_nndist] at hy,
      norm_cast at hy ⊢,
      exact hy, },
    exact (hfp n).antideriv_has_deriv_at this, },
  have hFG : tendsto (λ n, F n x) l (𝓝 (G x)),
  { refine tendsto_nhds_lim ⟨0, _⟩,
    have : ∀ n, F n x = 0,
    { intros n,
      have := (hfp n).antideriv_has_fpower_series_on_ball.coeff_zero,
      simp only [formal_multilinear_series.antideriv, real.coe_to_nnreal',
        continuous_multilinear_map.zero_apply, fin.forall_fin_zero_pi] at this,
      exact this.symm, },
    simp_rw this,
    exact tendsto_const_nhds, },
  have hFG' := hfg.mono (metric.ball_subset_closed_ball.trans hr'),
  have hFG : ∀ y, y ∈ metric.ball x r → tendsto (λ n, F n y) l (𝓝 (G y)),
  { intros y hy,
    have := uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_deriv hr hF hFG
      hFG'.uniform_cauchy_seq_on,
    have : cauchy (map (λ n, F n y) l),
    { rw metric.cauchy_iff,
      split,
      { exact filter.map_ne_bot, },
      intros ε hε,
      obtain ⟨N, hN, hNm⟩ := (metric.uniform_cauchy_seq_on_iff'.mp this) ε hε,
      refine ⟨_, image_mem_map hN, λ m hm n hn, _⟩,
      obtain ⟨m', hm'⟩ := hm,
      obtain ⟨n', hn'⟩ := hn,
      simp only at hm' hn',
      rw [←hm'.2, ←hn'.2],
      exact hNm m' hm'.1 n' hn'.1 y hy, },
    rw cauchy_map_iff_exists_tendsto at this,
    simpa using tendsto_nhds_lim this, },

  -- Since the `F` converge to `G`, we can use `has_deriv_at_of_tendsto_uniformly_on` to show that
  -- the derivative of `G` is `g` at `x`
  have : is_open (metric.ball x r), exact metric.is_open_ball,
  have hfin := has_deriv_at_of_tendsto_uniformly_on this hF hFG
    (hfg.mono (metric.ball_subset_closed_ball.trans hr')),

  -- Our second use of `ℂ`: differentiability implies analyticity
  have : analytic_on ℂ G (metric.ball x r),
  { intros y hy,
    have : metric.ball x r ∈ 𝓝 y,
    { exact mem_nhds_iff.mpr ⟨metric.ball x r, rfl.subset, metric.is_open_ball, hy⟩, },
    refine differentiable_on.analytic_at _ this,
    intros z hz,
    exact (hfin z hz).differentiable_at.differentiable_within_at, },

  -- Analyticity implies the derivative is analytic
  obtain ⟨p, ⟨R, hR⟩⟩ := (this.deriv x (metric.mem_ball_self hr)),

  -- The `congr` for replacing `deriv G` with `g` requires us to show that `deriv G` and
  -- `g` match on a small ball around `x`. So shrink radii further so we can apply `hfin`
  obtain ⟨R', hlR', hrR'⟩ := ennreal.lt_iff_exists_nnreal_btwn.mp hR.r_pos,
  use [p, min R' r],
  have hR' := hR.mono hlR' hrR'.le,
  refine (hR'.mono (by simp [lt_min, hR'.r_pos, hr]) (min_le_left R' r)).congr _,

  -- Finally, apply `hfin` on this small ball
  intros y hy,
  simp only [emetric.mem_ball, lt_min_iff, edist_lt_coe] at hy,
  exact (hfin y hy.2).deriv,
end

/-- If a sequence of holomorphic functions converges uniformly on a domain, then the
limit is also holomorphic on the domain -/
theorem complex.analytic_on_of_tendsto_uniformly_on (hs : is_open s)
  (hf : ∀ (n : η), analytic_on ℂ (f n) s)
  (hfg : tendsto_uniformly_on f g l s) : analytic_on ℂ g s :=
λ x hx, complex.analytic_at_of_tendsto_uniformly_on
  (mem_nhds_iff.mpr ⟨s, rfl.subset, hs, hx⟩) hf hfg

end complex
