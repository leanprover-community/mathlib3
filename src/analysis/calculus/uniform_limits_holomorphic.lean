/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
-- import analysis.analytic.basic
-- import analysis.complex.cauchy_integral
-- import ring_theory.power_series.basic
-- import linear_algebra.multilinear.basic
-- import analysis.normed.field.basic
import analysis.calculus.fderiv_analytic
-- import analysis.calculus.uniform_limits_deriv

/-!
# Uniform limits of holomorphic functions are holomorphic

The purpose of this file is to prove that a uniform limit of holomorphic functions is holomorphic,
a critical component of many theories, notably that of Dirichlet series.

## Main statements

* `analytic_at_of_tendsto_uniformly_on_filter` : If `f : ℕ → ℂ → ℂ` is a sequence functions which
  are analytic at `x` and they converge _uniformly_ to `g : ℂ → ℂ` on `𝓝 x`, then `f` is also
  analytic at `x`

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

uniform convergence, holomorphic functions
-/

open_locale big_operators

variables {ι 𝕜 E F : Type*} [fintype ι] [decidable_eq ι]

section general

lemma foo₁ [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] (f : multilinear_map 𝕜 (λ i : ι, 𝕜) E)
  (x : ι → 𝕜) : f x = (∏ i, x i) • (f 1) :=
begin
  rw ← multilinear_map.map_smul_univ,
  exact congr_arg f (funext $ λ i, by simp)
end

lemma foo₂ [comm_semiring 𝕜] (f : multilinear_map 𝕜 (λ i : ι, 𝕜) 𝕜)
  (x : ι → 𝕜) : f x = (f 1) * (∏ i, x i) :=
by rw [foo₁, smul_eq_mul, mul_comm]

lemma bar₁ [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space 𝕜] [topological_space E]
  (f : continuous_multilinear_map 𝕜 (λ i : ι, 𝕜) E)
  (x : ι → 𝕜) : f x = (∏ i, x i) • (f 1) :=
foo₁ f.to_multilinear_map x

lemma bar₂ [comm_semiring 𝕜] [topological_space 𝕜]
  (f : continuous_multilinear_map 𝕜 (λ i : ι, 𝕜) 𝕜)
  (x : ι → 𝕜) : f x = (f 1) * (∏ i, x i) :=
foo₂ f.to_multilinear_map x

lemma sum₁ [comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [topological_space E] [topological_add_group E] [has_continuous_const_smul 𝕜 E]
  (φ : formal_multilinear_series 𝕜 𝕜 E) (x : 𝕜) :
  φ.sum x = ∑' (n : ℕ), x^n • (φ n 1) :=
begin
  rw formal_multilinear_series.sum,
  congr,
  ext n,
  rw [bar₁, fin.prod_const]
end

lemma sum₂ [comm_ring 𝕜]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  (φ : formal_multilinear_series 𝕜 𝕜 𝕜) (x : 𝕜) :
  φ.sum x = ∑' (n : ℕ), (φ n 1) * x^n :=
begin
  rw formal_multilinear_series.sum,
  congr,
  ext n,
  rw [bar₂, fin.prod_const]
end

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

lemma partial_sum₂ [comm_ring 𝕜]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  (φ : formal_multilinear_series 𝕜 𝕜 𝕜) (x : 𝕜) (n : ℕ) :
  φ.partial_sum n x = ∑ k in finset.range n, (φ k 1) * x^k :=
begin
  rw formal_multilinear_series.partial_sum,
  congr,
  ext n,
  rw [bar₂, fin.prod_const],
end

lemma partial_sum₃ [comm_ring 𝕜]
  [topological_space 𝕜] [topological_add_group 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  (φ : formal_multilinear_series 𝕜 𝕜 𝕜) (n : ℕ) :
  φ.partial_sum n = (λ x, ∑ k in finset.range n, (φ k 1) * x^k) :=
begin
  ext,
  rw formal_multilinear_series.partial_sum,
  congr,
  ext n,
  rw [bar₂, fin.prod_const],
end

end general

section normed_field
variables [normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

def formal_multilinear_series.antideriv (φ : formal_multilinear_series 𝕜 𝕜 E) : formal_multilinear_series 𝕜 𝕜 E
| 0 := 0
| (n + 1) := ((n + 1) : 𝕜)⁻¹ • (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 (n + 1) 𝕜).smul_right (φ n 1)

end normed_field

section nontrivially_normed_field
-- TODO: Why doesn't `nontrivially_normed_field` get imported?
variables [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
  {φ : formal_multilinear_series 𝕜 𝕜 E}

lemma antideriv_radius_mono {r : nnreal}
  -- φ.radius ≤ φ.antideriv.radius :=
  (hr : ↑r < φ.radius) : ↑r ≤ φ.antideriv.radius :=
begin
  -- suffices : ∀ (r : nnreal), ↑r < φ.radius → ↑r ≤ φ.antideriv.radius,
  -- {
  --   intros r hr,
  --   by_contradiction h,
  --   push_neg at h,
  --   obtain ⟨r, hr, hr'⟩ := ennreal.lt_iff_exists_nnreal_btwn.mp (this r hr),
  --   -- exact not_lt_of_le rfl.le (lt_of_lt_of_le hr (antideriv_radius_mono hr')),
  -- },
  -- intros r hr,
  obtain ⟨C, hC, hm⟩ := φ.norm_mul_pow_le_of_lt_radius hr,
  refine formal_multilinear_series.le_radius_of_bound _ (C * r) _,
  intros n,
  induction n with n hn,
  simp only [formal_multilinear_series.antideriv, norm_zero, zero_mul],
  refine mul_nonneg hC.lt.le nnreal.zero_le_coe,

  have : n.succ = n + 1, refl,
  rw this,
  dunfold formal_multilinear_series.antideriv,
  rw norm_smul,
  have : ∥(continuous_multilinear_map.mk_pi_algebra_fin 𝕜 (n + 1) 𝕜).smul_right ((φ n) 1)∥ = ∥(continuous_multilinear_map.mk_pi_algebra_fin 𝕜 (n + 1) 𝕜)∥ * ∥((φ n) 1)∥, {
    rw continuous_multilinear_map.norm_def,
    simp,
    simp [has_norm.norm],
    ext,

  },
  simp only [continuous_multilinear_map.norm_mk_pi_algebra_fin, mul_one],
  rw [pow_add (r : ℝ) n 1, ←mul_assoc, pow_one],
  refine mul_le_mul _ rfl.le nnreal.zero_le_coe hC.lt.le,
  rw [norm_mul, mul_assoc],
  have : C = 1 * C, simp,
  rw this,
  have : ∥φ n 1∥ ≤ ∥φ n∥,
  { convert continuous_multilinear_map.unit_le_op_norm _ 1 _,
    { refl },
    { have : (1 : fin n → ℂ) = (λ i, 1), { ext, refl, refl, },
      rw this,
      simp only [has_norm.norm, nnnorm_one],
      norm_cast,
      rw finset.sup_le_iff,
      intros b hb,
      exact rfl.le, } },
  refine mul_le_mul _
    ((mul_le_mul this rfl.le (by simp only [pow_nonneg, nnreal.zero_le_coe]) (norm_nonneg _)).trans (hm n))
    (mul_nonneg (norm_nonneg _) (by simp only [pow_nonneg, nnreal.zero_le_coe]))
    zero_le_one,

  rw norm_inv,
  have : (n : ℂ) + 1 = (((n + 1) : ℝ) : ℂ), norm_cast,
  rw this,
  norm_cast,
  rw inv_le _ _,
  rw real.norm_of_nonneg _,
  simp only [inv_one, nat.cast_add, nat.cast_one, le_add_iff_nonneg_left, nat.cast_nonneg],
  norm_cast,
  simp only [zero_le'],

  simp only [nat.cast_add, nat.cast_one, real.norm_eq_abs, abs_pos, ne.def],
  norm_cast,
  simp only [nat.succ_ne_zero, not_false_iff],

  simp only [zero_lt_one],
end

-- The proof is by approximation below coupled with the above lemma
lemma antideriv_radius_mono':
  φ.radius ≤ (pad φ).radius :=
begin
  by_contradiction h,
  push_neg at h,
  obtain ⟨r, hr, hr'⟩ := ennreal.lt_iff_exists_nnreal_btwn.mp h,
  exact not_lt_of_le rfl.le (lt_of_lt_of_le hr (antideriv_radius_mono hr')),
end

lemma blahblah {y : ℂ} {n : ℕ} :
  has_deriv_at (λ z : ℂ, (pad φ) (n + 1) (λ i : fin (n + 1), z)) (φ n (λ i : fin n, y)) y :=
begin
  rw bar₂,
  conv {
    congr, funext, rw bar₂, rw fin.prod_const,
  },
  rw fin.prod_const,
  have : pad φ (n + 1) 1 = ((n + 1) : ℂ)⁻¹ * (φ n 1), {
    simp only [pad],
    rw continuous_multilinear_map.smul_apply,
    simp only [continuous_multilinear_map.mk_pi_algebra_fin_apply, list.of_fn_succ, pi.one_apply, list.of_fn_const, list.prod_cons,
  list.prod_repeat, one_pow, mul_one, algebra.id.smul_eq_mul],
  },
  rw this,
  -- Now need to pull out the const with has_deriv_at_const
  sorry,
end

lemma blahblah2 {y : ℂ} {n : ℕ} :
  has_deriv_at ((pad φ).partial_sum n.succ) (φ.partial_sum n y) y :=
begin
  rw partial_sum₂,
  rw partial_sum₃,
  induction n with n hn,
  simp only [finset.range_one, finset.sum_singleton, pow_zero, mul_one, finset.range_zero, finset.sum_empty, pad, continuous_multilinear_map.zero_apply],
  exact has_deriv_at_const y 0,
  rw finset.sum_range_succ,
  conv {
    congr, funext, rw finset.sum_range_succ,
  },
  refine has_deriv_at.add hn _,
  dunfold pad,
  simp only [continuous_multilinear_map.smul_apply, continuous_multilinear_map.mk_pi_algebra_fin_apply, list.of_fn_succ, pi.one_apply, list.of_fn_const, list.prod_cons, list.prod_repeat, one_pow, mul_one, algebra.id.smul_eq_mul],
  have : n.succ = n + 1, simp,
  rw this,
  have : (φ n (λ i : fin n, y)) = ((φ n) 1 * y ^ n), { rw bar₂, rw fin.prod_const, },
  rw ← this,
  refine blahblah.congr_of_eventually_eq _,
  apply filter.eventually_of_forall,
  intros z,
  simp only [pad, list.repeat_succ, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, continuous_multilinear_map.smul_apply, continuous_multilinear_map.mk_pi_algebra_fin_apply, list.of_fn_succ, pi.one_apply, list.of_fn_const, list.prod_cons, list.prod_repeat, one_pow, mul_one, algebra.id.smul_eq_mul],
  left,
  rw ←pow_one z,
  rw pow_add,
  rw mul_comm,
  simp,
end

lemma blahblah3 {y : ℂ} (hφ : 0 < φ.radius) (hy' : y ∈ emetric.ball (0 : ℂ) φ.radius):
  has_deriv_at (pad φ).sum (φ.sum y) y :=
begin
  -- For technical reasons involving uniform convergence, we need to shrink our radius
  obtain ⟨r, hr, hr'⟩ : ∃ (r : nnreal), nndist y 0 < r ∧ ↑r < φ.radius,
  { suffices : ∃ (r : nnreal), ((nndist y 0) : ennreal) < r ∧ ↑r < φ.radius,
    { obtain ⟨r, hr, hr'⟩ := this,
      refine ⟨r, (by simpa using hr), hr'⟩, },
    exact ennreal.lt_iff_exists_nnreal_btwn.mp hy', },

  have h1 : is_open (metric.ball (0 : ℂ) r), exact metric.is_open_ball,
  have h2 : ∀ n : ℕ, ∀ z : ℂ, z ∈ metric.ball (0 : ℂ) r → has_deriv_at ((pad φ).partial_sum n.succ) (φ.partial_sum n z) z, {
    intros n z hz,
    exact blahblah2,
  },
  have foo : filter.tendsto (λ n : ℕ, n.succ) filter.at_top filter.at_top, {
    rw filter.tendsto_at_top_at_top_iff_of_monotone,
    intros b,
    use b,
    exact nat.le_succ b,
    intros m n hmn,
    exact nat.succ_le_succ hmn,
  },
  have h3 : ∀ z : ℂ, z ∈ metric.ball (0 : ℂ) r → filter.tendsto (λ n : ℕ, (pad φ).partial_sum n.succ z) filter.at_top (nhds ((pad φ).sum z)), {
    intros z hz,
    suffices : filter.tendsto (λ (n : ℕ), (pad φ).partial_sum n z) filter.at_top (nhds ((pad φ).sum z)), {
      exact this.comp foo,
    },
    have : 0 < (pad φ).radius, exact lt_of_lt_of_le hφ antideriv_radius_mono',
    have hh2 : ↑r < (pad φ).radius, exact lt_of_lt_of_le hr' antideriv_radius_mono',
    simpa using (((pad φ).has_fpower_series_on_ball this).tendsto_uniformly_on hh2).tendsto_at hz,
  },
  have h4 : tendsto_uniformly_on (λ (n : ℕ) (z : ℂ), φ.partial_sum n z) φ.sum filter.at_top (metric.ball 0 r), {
    simpa using (φ.has_fpower_series_on_ball hφ).tendsto_uniformly_on hr',
  },
  exact has_deriv_at_of_tendsto_uniformly_on h1 h2 h3 h4 y hr,
end

end nontrivially_normed_field

section is_R_or_C

open filter
open_locale filter topological_space

variables
  {f : ℕ → ℂ → ℂ}
  {g : ℂ → ℂ}
  {p : formal_multilinear_series ℂ ℂ ℂ}
  {x : ℂ}
  {r : ennreal}

noncomputable def antideriv_func
  (h : has_fpower_series_on_ball g p x r) : ℂ → ℂ :=
λ z, (pad p).sum (z - x)

lemma antideriv_func_has_fpower_series_on_ball
  (h : has_fpower_series_on_ball g p x r) :
  has_fpower_series_on_ball (antideriv_func h) (pad p) x r :=
begin
  have : x = 0 + x, simp,
  conv {congr, skip, skip, rw this,},
  dunfold antideriv_func,
  apply has_fpower_series_on_ball.comp_sub,
  refine has_fpower_series_on_ball.mono _ h.r_pos (h.r_le.trans antideriv_radius_mono'),
  refine (pad p).has_fpower_series_on_ball _,
  calc 0 < r : h.r_pos
    ... ≤ p.radius : h.r_le
    ... ≤ (pad p).radius : antideriv_radius_mono',
end

lemma antideriv_func_has_deriv_at
  (h : has_fpower_series_on_ball g p x r) {y : ℂ} (hy : y ∈ emetric.ball x r) :
  has_deriv_at (antideriv_func h) (g y) y :=
begin
  let recenter : ℂ → ℂ := (λ z, z - x),
  have : (antideriv_func h) = (pad p).sum ∘ recenter,
  {
    funext,
    simp [antideriv_func, pad, recenter],
  },
  rw this,
  have : y - x ∈ emetric.ball (0 : ℂ) p.radius, sorry,
  have := blahblah3 (lt_of_lt_of_le h.r_pos h.r_le) this,
  have ugh : y - x = recenter y, simp [recenter],
  conv at this {congr, skip, skip, rw ugh, },
  have bah : has_deriv_at recenter 1 y, sorry,
  have aa := has_deriv_at.comp y this bah,
  have bb : g y = p.sum (y - x), sorry,
  rw ←bb at aa,
  simp at aa,
  exact aa,
end

/-- If a sequence of holomorphic functions converges uniformly on a ball around `x`, then the limit
is also holomorphic at `x` -/
theorem main_theorem
  {f : ℕ → ℂ → ℂ}
  {g : ℂ → ℂ}
  {x : ℂ}
  {s : set ℂ}
  (hs : s ∈ 𝓝 x)
  (hf : ∀ (n : ℕ), analytic_on ℂ (f n) s)
  (hfg : tendsto_uniformly_on f g at_top s) :
  analytic_at ℂ g x :=
begin
  obtain ⟨_r, h_r, h_r'⟩ := metric.nhds_basis_closed_ball.mem_iff.mp hs,
  let r : nnreal := _r.to_nnreal,
  have hr : 0 < r, exact real.to_nnreal_pos.mpr h_r,
  have : max _r 0 = _r, {
    exact max_eq_left_of_lt h_r,
  },
  have hr' : metric.closed_ball x r ⊆ s, {simp [this, h_r'], },

  have hf' : ∀ n : ℕ, differentiable_on ℂ (f n) (metric.closed_ball x r), {
    intros n y hy,
    exact (hf n y (set.mem_of_mem_of_subset hy hr')).differentiable_at.differentiable_within_at,
  },

  have hf'' : ∀ n : ℕ, has_fpower_series_on_ball (f n) (cauchy_power_series (f n) x r) x r, {
    intros n,
    exact (hf' n).has_fpower_series_on_ball hr,
  },

  let F : ℕ → ℂ → ℂ := (λ n : ℕ, antideriv_func (hf'' n)),
  let G : ℂ → ℂ := (λ z : ℂ, lim at_top (λ n : ℕ, F n z)),

  have hF : ∀ (n : ℕ), ∀ (y : ℂ), y ∈ metric.ball x r → has_deriv_at (F n) (f n y) y,
  { intros n y hy,
    have : y ∈ emetric.ball x r,
    { rw [emetric.mem_ball, edist_nndist],
      rw [metric.mem_ball, dist_nndist] at hy,
      norm_cast at hy ⊢,
      exact hy, },
    exact antideriv_func_has_deriv_at (hf'' n) this, },
  have foo : tendsto (λ n, F n x) at_top (𝓝 (G x)),
  { apply tendsto_nhds_lim,
    use 0,
    have : ∀ n, F n x = 0,
    { intros n,
      have := (antideriv_func_has_fpower_series_on_ball (hf'' n)).coeff_zero,
      simp [pad] at this,
      exact this.symm, },
    simp_rw this,
    exact tendsto_const_nhds, },
  have hfgg := hfg.mono (metric.ball_subset_closed_ball.trans hr'),
  have hFG : ∀ (y : ℂ), y ∈ metric.ball x r → tendsto (λ n : ℕ, F n y) at_top (𝓝 (G y)),
  {
    intros y hy,
    have := uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_deriv hr hF foo hfgg.uniform_cauchy_seq_on,
    have : cauchy_seq (λ n : ℕ, F n y), {
      rw metric.cauchy_seq_iff,
      intros ε hε,
      rw metric.uniform_cauchy_seq_on_iff at this,
      obtain ⟨N, hN⟩ := this ε hε,
      use N,
      intros m hm n hn,
      exact hN m hm n hn y hy,
    },
    simpa using this.tendsto_lim,
  },
  have : is_open (metric.ball x r), exact metric.is_open_ball,
  have foo := has_deriv_at_of_tendsto_uniformly_on this hF hFG (hfg.mono (metric.ball_subset_closed_ball.trans hr')),
  have : analytic_on ℂ G (metric.ball x r), {
    intros y hy,
    have : metric.ball x r ∈ 𝓝 y,
    { exact mem_nhds_iff.mpr ⟨metric.ball x r, rfl.subset, metric.is_open_ball, hy⟩, },
    refine differentiable_on.analytic_at _ this,
    intros z hz,
    exact (foo z hz).differentiable_at.differentiable_within_at,
  },
  obtain ⟨p, ⟨R, hR⟩⟩ := (this.deriv x (metric.mem_ball_self hr)),
  obtain ⟨R', hlR', hrR'⟩ := ennreal.lt_iff_exists_nnreal_btwn.mp hR.r_pos,
  use [p, min R' r],
  have hR' := hR.mono hlR' hrR'.le,
  refine (hR'.mono (by simp [lt_min, hR'.r_pos, hr]) (min_le_left R' r)).congr _,
  intros y hy,
  simp at hy,
  exact (foo y hy.2).deriv,
end

end is_R_or_C
