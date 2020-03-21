/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.times_cont_diff tactic.omega analysis.complex.exponential
analysis.specific_limits

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ennreal` such that `∥p n∥ * r^n` grows subexponentially, defined as
  a liminf.
* `p.le_radius_of_bound`, `p.bound_of_lt_radius`, `p.geometric_bound_of_lt_radius`: relating the
  value of the radius with the growth of `∥p n∥ * r^n`.
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]

open_locale topological_space classical
open filter

/-! ### The radius of a formal multilinear series -/

namespace formal_multilinear_series

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ pₙ yⁿ`
converges for all `∥y∥ < r`. -/
def radius (p : formal_multilinear_series 𝕜 E F) : ennreal :=
liminf at_top (λ n, 1/((nnnorm (p n)) ^ (1 / (n : ℝ)) : nnreal))

/--If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_bound (p : formal_multilinear_series 𝕜 E F) (C : nnreal) {r : nnreal}
  (h : ∀ (n : ℕ), nnnorm (p n) * r^n ≤ C) : (r : ennreal) ≤ p.radius :=
begin
  have L : tendsto (λ n : ℕ, (r : ennreal) / ((C + 1)^(1/(n : ℝ)) : nnreal))
    at_top (𝓝 ((r : ennreal) / ((C + 1)^(0 : ℝ) : nnreal))),
  { apply ennreal.tendsto.div tendsto_const_nhds,
    { simp },
    { rw ennreal.tendsto_coe,
      apply tendsto_const_nhds.nnrpow (tendsto_const_div_at_top_nhds_0_nat 1),
      simp },
    { simp } },
  have A : ∀ n : ℕ , 0 < n →
    (r : ennreal) ≤ ((C + 1)^(1/(n : ℝ)) : nnreal) * (1 / (nnnorm (p n) ^ (1/(n:ℝ)) : nnreal)),
  { assume n npos,
    simp only [one_div_eq_inv, mul_assoc, mul_one, eq.symm ennreal.mul_div_assoc],
    rw [ennreal.le_div_iff_mul_le _ _, ← nnreal.pow_nat_rpow_nat_inv r npos, ← ennreal.coe_mul,
        ennreal.coe_le_coe, ← nnreal.mul_rpow, mul_comm],
    { exact nnreal.rpow_le_rpow (le_trans (h n) (le_add_right (le_refl _))) (by simp) },
    { simp },
    { simp } },
  have B : ∀ᶠ (n : ℕ) in at_top,
    (r : ennreal) / ((C + 1)^(1/(n : ℝ)) : nnreal) ≤ 1 / (nnnorm (p n) ^ (1/(n:ℝ)) : nnreal),
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    rw [ennreal.div_le_iff_le_mul, mul_comm],
    { apply A n hn },
    { simp },
    { simp } },
  have D : liminf at_top (λ n : ℕ, (r : ennreal) / ((C + 1)^(1/(n : ℝ)) : nnreal)) ≤ p.radius :=
    liminf_le_liminf B,
  rw liminf_eq_of_tendsto filter.at_top_ne_bot L at D,
  simpa using D
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
lemma bound_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : nnreal}
  (h : (r : ennreal) < p.radius) : ∃ (C : nnreal), ∀ n, nnnorm (p n) * r^n ≤ C :=
begin
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ n, n ≥ N → (r : ennreal) < 1 / ↑(nnnorm (p n) ^ (1 / (n : ℝ))) :=
    eventually.exists_forall_of_at_top (eventually_lt_of_lt_liminf h),
  obtain ⟨D, hD⟩ : ∃D, ∀ x ∈ (↑((finset.range N.succ).image (λ i, nnnorm (p i) * r^i))), x ≤ D :=
    finset.bdd_above _,
  refine ⟨max D 1, λ n, _⟩,
  cases le_or_lt n N with hn hn,
  { refine le_trans _ (le_max_left D 1),
    apply hD,
    have : n ∈ finset.range N.succ := list.mem_range.mpr (nat.lt_succ_iff.mpr hn),
    exact finset.mem_image_of_mem _ this },
  { by_cases hpn : nnnorm (p n) = 0, { simp [hpn] },
    have A : nnnorm (p n) ^ (1 / (n : ℝ)) ≠ 0, by simp [nnreal.rpow_eq_zero_iff, hpn],
    have B : r < (nnnorm (p n) ^ (1 / (n : ℝ)))⁻¹,
    { have := hN n (le_of_lt hn),
      rwa [ennreal.div_def, ← ennreal.coe_inv A, one_mul, ennreal.coe_lt_coe] at this },
    rw [nnreal.lt_inv_iff_mul_lt A, mul_comm] at B,
    have : (nnnorm (p n) ^ (1 / (n : ℝ)) * r) ^ n ≤ 1 :=
      pow_le_one n (zero_le (nnnorm (p n) ^ (1 / ↑n) * r)) (le_of_lt B),
    rw [mul_pow, one_div_eq_inv, nnreal.rpow_nat_inv_pow_nat _ (lt_of_le_of_lt (zero_le _) hn)]
      at this,
    exact le_trans this (le_max_right _ _) },
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially. -/
lemma geometric_bound_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : nnreal}
  (h : (r : ennreal) < p.radius) : ∃ a C, a < 1 ∧ ∀ n, nnnorm (p n) * r^n ≤ C * a^n :=
begin
  obtain ⟨t, rt, tp⟩ : ∃ t, (r : ennreal) < t ∧ t < p.radius := dense h,
  cases t, { simpa using tp },
  simp only [ennreal.some_eq_coe, ennreal.coe_lt_coe] at rt,
  have tpos : t ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le _) rt),
  obtain ⟨C, hC⟩ : ∃ (C : nnreal), ∀ n, nnnorm (p n) * t^n ≤ C := p.bound_of_lt_radius tp,
  refine ⟨r / t, C, nnreal.div_lt_one_of_lt rt, λ n, _⟩,
  calc nnnorm (p n) * r ^ n
    = (nnnorm (p n) * t ^ n) * (r / t) ^ n : by { field_simp [tpos], ac_refl }
    ... ≤ C * (r / t) ^ n : mul_le_mul_of_nonneg_right (hC n) (zero_le _)
end

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
lemma min_radius_le_radius_add (p q : formal_multilinear_series 𝕜 E F) :
  min p.radius q.radius ≤ (p + q).radius :=
begin
  refine le_of_forall_ge_of_dense (λ r hr, _),
  cases r, { simpa using hr },
  obtain ⟨Cp, hCp⟩ : ∃ (C : nnreal), ∀ n, nnnorm (p n) * r^n ≤ C :=
    p.bound_of_lt_radius (lt_of_lt_of_le hr (min_le_left _ _)),
  obtain ⟨Cq, hCq⟩ : ∃ (C : nnreal), ∀ n, nnnorm (q n) * r^n ≤ C :=
    q.bound_of_lt_radius (lt_of_lt_of_le hr (min_le_right _ _)),
  have : ∀ n, nnnorm ((p + q) n) * r^n ≤ Cp + Cq,
  { assume n,
    calc nnnorm (p n + q n) * r ^ n
    ≤ (nnnorm (p n) + nnnorm (q n)) * r ^ n :
      mul_le_mul_of_nonneg_right (norm_add_le (p n) (q n)) (zero_le (r ^ n))
    ... ≤ Cp + Cq : by { rw add_mul, exact add_le_add (hCp n) (hCq n) } },
  exact (p + q).le_radius_of_bound _ this
end

lemma radius_neg (p : formal_multilinear_series 𝕜 E F) : (-p).radius = p.radius :=
by simp [formal_multilinear_series.radius, nnnorm_neg]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `∥x∥ < p.radius`. -/
def sum (p : formal_multilinear_series 𝕜 E F) (x : E) : F :=
tsum (λn:ℕ, p n (λ(i : fin n), x))

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partial_sum (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (x : E) : F :=
(finset.range n).sum (λ k, p k (λ(i : fin k), x))

/-- The partial sums of a formal multilinear series are continuous. -/
lemma partial_sum_continuous (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  continuous (p.partial_sum n) :=
continuous_finset_sum (finset.range n) $ λ k hk, (p k).cont.comp (continuous_pi (λ i, continuous_id))

end formal_multilinear_series


/-! ### Expanding a function as a power series -/

variables {f g : E → F} {p pf pg : formal_multilinear_series 𝕜 E F} {x : E} {r r' : ennreal}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑ pₙ yⁿ` for all `∥y∥ < r`. -/
structure has_fpower_series_on_ball
  (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) (r : ennreal) : Prop :=
(r_le    : r ≤ p.radius)
(r_pos   : 0 < r)
(has_sum : ∀ {y}, y ∈ emetric.ball (0 : E) r → has_sum (λn:ℕ, p n (λ(i : fin n), y)) (f (x + y)))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑ pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def has_fpower_series_at (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) :=
∃ r, has_fpower_series_on_ball f p x r

variable (𝕜)
/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def analytic_at (f : E → F) (x : E) :=
∃ (p : formal_multilinear_series 𝕜 E F), has_fpower_series_at f p x

variable {𝕜}

lemma has_fpower_series_on_ball.has_fpower_series_at (hf : has_fpower_series_on_ball f p x r) :
  has_fpower_series_at f p x := ⟨r, hf⟩

lemma has_fpower_series_at.analytic_at (hf : has_fpower_series_at f p x) : analytic_at 𝕜 f x :=
⟨p, hf⟩

lemma has_fpower_series_on_ball.analytic_at (hf : has_fpower_series_on_ball f p x r) :
  analytic_at 𝕜 f x :=
hf.has_fpower_series_at.analytic_at

lemma has_fpower_series_on_ball.radius_pos (hf : has_fpower_series_on_ball f p x r) :
  0 < p.radius :=
lt_of_lt_of_le hf.r_pos hf.r_le

lemma has_fpower_series_at.radius_pos (hf : has_fpower_series_at f p x) :
  0 < p.radius :=
let ⟨r, hr⟩ := hf in hr.radius_pos

lemma has_fpower_series_on_ball.mono
  (hf : has_fpower_series_on_ball f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
  has_fpower_series_on_ball f p x r' :=
⟨le_trans hr hf.1, r'_pos, λ y hy, hf.has_sum (emetric.ball_subset_ball hr hy)⟩

lemma has_fpower_series_on_ball.add
  (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) :
  has_fpower_series_on_ball (f + g) (pf + pg) x r :=
{ r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg),
  r_pos := hf.r_pos,
  has_sum := λ y hy, (hf.has_sum hy).add (hg.has_sum hy) }

lemma has_fpower_series_at.add
  (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) :
  has_fpower_series_at (f + g) (pf + pg) x :=
begin
  rcases hf with ⟨rf, hrf⟩,
  rcases hg with ⟨rg, hrg⟩,
  have P : 0 < min rf rg, by simp [hrf.r_pos, hrg.r_pos],
  exact ⟨min rf rg, (hrf.mono P (min_le_left _ _)).add (hrg.mono P (min_le_right _ _))⟩
end

lemma analytic_at.add (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) :
  analytic_at 𝕜 (f + g) x :=
let ⟨pf, hpf⟩ := hf, ⟨qf, hqf⟩ := hg in (hpf.add hqf).analytic_at

lemma has_fpower_series_on_ball.neg (hf : has_fpower_series_on_ball f pf x r) :
  has_fpower_series_on_ball (-f) (-pf) x r :=
{ r_le    := by { rw pf.radius_neg, exact hf.r_le },
  r_pos   := hf.r_pos,
  has_sum := λ y hy, (hf.has_sum hy).neg }

lemma has_fpower_series_at.neg
  (hf : has_fpower_series_at f pf x) : has_fpower_series_at (-f) (-pf) x :=
let ⟨rf, hrf⟩ := hf in hrf.neg.has_fpower_series_at

lemma analytic_at.neg (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (-f) x :=
let ⟨pf, hpf⟩ := hf in hpf.neg.analytic_at

lemma has_fpower_series_on_ball.sub
  (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) :
  has_fpower_series_on_ball (f - g) (pf - pg) x r :=
hf.add hg.neg

lemma has_fpower_series_at.sub
  (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) :
  has_fpower_series_at (f - g) (pf - pg) x :=
hf.add hg.neg

lemma analytic_at.sub (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) :
  analytic_at 𝕜 (f - g) x :=
hf.add hg.neg

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
lemma has_fpower_series_on_ball.uniform_limit {r' : nnreal}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ennreal) < r) :
  ∃ (a C : nnreal), a < 1 ∧ (∀ y ∈ metric.ball (0 : E) r', ∀ n,
  ∥f (x + y) - p.partial_sum n y∥ ≤ C * a ^ n) :=
begin
  obtain ⟨a, C, ha, hC⟩ : ∃ a C, a < 1 ∧ ∀ n, nnnorm (p n) * r' ^n ≤ C * a^n :=
    p.geometric_bound_of_lt_radius (lt_of_lt_of_le h hf.r_le),
  refine ⟨a, C / (1 - a), ha, λ y hy n, _⟩,
  have yr' : ∥y∥ < r', by { rw ball_0_eq at hy, exact hy },
  have : y ∈ emetric.ball (0 : E) r,
  { rw [emetric.mem_ball, edist_eq_coe_nnnorm],
    apply lt_trans _ h,
    rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe],
    exact yr' },
  simp only [nnreal.coe_sub (le_of_lt ha), nnreal.coe_sub, nnreal.coe_div, nnreal.coe_one],
  rw [← dist_eq_norm, dist_comm, dist_eq_norm, ← mul_div_right_comm],
  apply norm_sub_le_of_geometric_bound_of_has_sum ha _ (hf.has_sum this),
  assume n,
  calc ∥(p n) (λ (i : fin n), y)∥
    ≤ ∥p n∥ * (finset.univ.prod (λ i : fin n, ∥y∥)) : continuous_multilinear_map.le_op_norm _ _
    ... = nnnorm (p n) * (nnnorm y)^n : by simp
    ... ≤ nnnorm (p n) * r' ^ n :
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (nnreal.coe_nonneg _) (le_of_lt yr') _)
      (nnreal.coe_nonneg _)
    ... ≤ C * a ^ n : by exact_mod_cast hC n,
end

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
lemma has_fpower_series_on_ball.continuous_on
  (hf : has_fpower_series_on_ball f p x r) : continuous_on f (emetric.ball x r) :=
begin
  have : ∀ n, continuous_on (λ y, p.partial_sum n (y - x)) (emetric.ball x r) :=
    λ n, ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).continuous_on,
  apply continuous_on_of_locally_uniform_limit_of_continuous_on (λ y hy, _) this,
  have : (nnnorm (y - x) : ennreal) < r,
    by { rw ← edist_eq_coe_nnnorm_sub, exact hy },
  rcases dense this with ⟨r', xr', r'r⟩,
  cases r', { simpa using r'r },
  replace xr' : nnnorm (y - x) < r', by simpa using xr',
  refine ⟨metric.ball x r', _, λ ε εpos, _⟩,
  show metric.ball x r' ∈ nhds_within y (emetric.ball x r),
  { apply mem_nhds_within_of_mem_nhds,
    apply mem_nhds_sets metric.is_open_ball,
    change dist y x < r',
    rwa [dist_nndist, nnreal.coe_lt_coe, nndist_eq_nnnorm] },
  show ∃ (n : ℕ),
    ∀ z ∈ metric.ball x ↑r', dist (formal_multilinear_series.partial_sum p n (z - x)) (f z) ≤ ε,
  { obtain ⟨a, C, ha, hC⟩ : ∃ (a C : nnreal), a < 1 ∧ (∀ y ∈ metric.ball (0 : E) r', ∀ n,
      ∥f (x + y) - p.partial_sum n y∥ ≤ C * a ^ n) := hf.uniform_limit r'r,
    have L : tendsto (λ (n : ℕ), (C : ℝ) * a ^ n) at_top (𝓝 ((C : ℝ) * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 (a.2) ha),
    rw mul_zero at L,
    obtain ⟨n, hn⟩ : ∃ (n : ℕ), (C : ℝ) * a ^ n < ε :=
      eventually.exists ((tendsto_order.1 L).2 _ εpos) at_top_ne_bot,
    refine ⟨n, λ z hz, _⟩,
    have : z - x ∈ metric.ball (0 : E) r',
      by { rwa [metric.mem_ball, dist_eq_norm, ← dist_zero_right] at hz },
    rw [dist_eq_norm, norm_sub_rev],
    convert le_trans (hC _ this n) (le_of_lt hn),
    abel }
end

lemma has_fpower_series_at.continuous_at (hf : has_fpower_series_at f p x) : continuous_at f x :=
let ⟨r, hr⟩ := hf in hr.continuous_on.continuous_at (emetric.ball_mem_nhds x (hr.r_pos))

lemma analytic_at.continuous_at (hf : analytic_at 𝕜 f x) : continuous_at f x :=
let ⟨p, hp⟩ := hf in hp.continuous_at

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
lemma formal_multilinear_series.has_fpower_series_on_ball [complete_space F]
  (p : formal_multilinear_series 𝕜 E F) (h : 0 < p.radius) :
  has_fpower_series_on_ball p.sum p 0 p.radius :=
{ r_le    := le_refl _,
  r_pos   := h,
  has_sum := λ y hy, begin
    rw zero_add,
    replace hy : (nnnorm y : ennreal) < p.radius,
      by { convert hy, exact (edist_eq_coe_nnnorm _).symm },
    obtain ⟨a, C, ha, hC⟩ : ∃ a C, a < 1 ∧ ∀ n, nnnorm (p n) * (nnnorm y)^n ≤ C * a^n :=
      p.geometric_bound_of_lt_radius hy,
    refine (summable_of_norm_bounded (λ n, (C : ℝ) * a ^ n)
      ((summable_geometric a.2 ha).mul_left _) (λ n, _)).has_sum,
    calc ∥(p n) (λ (i : fin n), y)∥
      ≤ ∥p n∥ * (finset.univ.prod (λ i : fin n, ∥y∥)) : continuous_multilinear_map.le_op_norm _ _
      ... = nnnorm (p n) * (nnnorm y)^n : by simp
      ... ≤ C * a ^ n : by exact_mod_cast hC n
  end }

lemma has_fpower_series_on_ball.sum [complete_space F] (h : has_fpower_series_on_ball f p x r)
  {y : E} (hy : y ∈ emetric.ball (0 : E) r) : f (x + y) = p.sum y :=
begin
  have A := h.has_sum hy,
  have B := (p.has_fpower_series_on_ball h.radius_pos).has_sum (lt_of_lt_of_le hy h.r_le),
  simpa using has_sum_unique A B
end

/-- The sum of a converging power series is continuous in its disk of convergence. -/
lemma formal_multilinear_series.continuous_on [complete_space F] :
  continuous_on p.sum (emetric.ball 0 p.radius) :=
begin
  by_cases h : 0 < p.radius,
  { exact (p.has_fpower_series_on_ball h).continuous_on },
  { simp at h,
    simp [h, continuous_on_empty] }
end
