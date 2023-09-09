/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.formal_multilinear_series
import analysis.specific_limits.normed
import logic.equiv.fin
import topology.algebra.infinite_sum.module

/-!
# Analytic functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

* `p.radius`: the largest `r : ℝ≥0∞` such that `‖p n‖ * r^n` grows subexponentially.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_is_O`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.is_o_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`, `p.is_o_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_is_O`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.
* `analytic_on 𝕜 f s`: the function `f` is analytic at every point of `s`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

noncomputable theory

variables {𝕜 E F G : Type*}

open_locale topology classical big_operators nnreal filter ennreal
open set filter asymptotics

namespace formal_multilinear_series

variables [ring 𝕜] [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]
variables [topological_space E] [topological_space F]
variables [topological_add_group E] [topological_add_group F]
variables [has_continuous_const_smul 𝕜 E] [has_continuous_const_smul 𝕜 F]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`. -/
protected def sum (p : formal_multilinear_series 𝕜 E F) (x : E) : F := ∑' n : ℕ , p n (λ i, x)

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partial_sum (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (x : E) : F :=
∑ k in finset.range n, p k (λ(i : fin k), x)

/-- The partial sums of a formal multilinear series are continuous. -/
lemma partial_sum_continuous (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  continuous (p.partial_sum n) :=
by continuity

end formal_multilinear_series

/-! ### The radius of a formal multilinear series -/


variables [nontrivially_normed_field 𝕜]
[normed_add_comm_group E] [normed_space 𝕜 E]
[normed_add_comm_group F] [normed_space 𝕜 F]
[normed_add_comm_group G] [normed_space 𝕜 G]

namespace formal_multilinear_series

variables (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ‖pₙ‖ ‖y‖ⁿ`
converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ < r`, but these
definitions are *not* equivalent in general. -/
def radius (p : formal_multilinear_series 𝕜 E F) : ℝ≥0∞ :=
⨆ (r : ℝ≥0) (C : ℝ) (hr : ∀ n, ‖p n‖ * r ^ n ≤ C), (r : ℝ≥0∞)

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ (n : ℕ), ‖p n‖ * r^n ≤ C) :
  (r : ℝ≥0∞) ≤ p.radius :=
le_supr_of_le r $ le_supr_of_le C $ (le_supr (λ _, (r : ℝ≥0∞)) h)

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_bound_nnreal (C : ℝ≥0) {r : ℝ≥0} (h : ∀ (n : ℕ), ‖p n‖₊ * r^n ≤ C) :
  (r : ℝ≥0∞) ≤ p.radius :=
p.le_radius_of_bound C $ λ n, by exact_mod_cast (h n)

/-- If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_is_O (h : (λ n, ‖p n‖ * r^n) =O[at_top] (λ n, (1 : ℝ))) : ↑r ≤ p.radius :=
exists.elim (is_O_one_nat_at_top_iff.1 h) $ λ C hC, p.le_radius_of_bound C $
  λ n, (le_abs_self _).trans (hC n)

lemma le_radius_of_eventually_le (C) (h : ∀ᶠ n in at_top, ‖p n‖ * r ^ n ≤ C) : ↑r ≤ p.radius :=
p.le_radius_of_is_O $ is_O.of_bound C $ h.mono $ λ n hn, by simpa

lemma le_radius_of_summable_nnnorm (h : summable (λ n, ‖p n‖₊ * r ^ n)) : ↑r ≤ p.radius :=
p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) $ λ n, le_tsum' h _

lemma le_radius_of_summable (h : summable (λ n, ‖p n‖ * r ^ n)) : ↑r ≤ p.radius :=
p.le_radius_of_summable_nnnorm $ by { simp only [← coe_nnnorm] at h, exact_mod_cast h }

lemma radius_eq_top_of_forall_nnreal_is_O
  (h : ∀ r : ℝ≥0, (λ n, ‖p n‖ * r^n) =O[at_top] (λ n, (1 : ℝ))) : p.radius = ∞ :=
ennreal.eq_top_of_forall_nnreal_le $ λ r, p.le_radius_of_is_O (h r)

lemma radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in at_top, p n = 0) : p.radius = ∞ :=
p.radius_eq_top_of_forall_nnreal_is_O $
  λ r, (is_O_zero _ _).congr' (h.mono $ λ n hn, by simp [hn]) eventually_eq.rfl

lemma radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) : p.radius = ∞ :=
p.radius_eq_top_of_eventually_eq_zero $ mem_at_top_sets.2
  ⟨n, λ k hk, tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp] lemma const_formal_multilinear_series_radius {v : F} :
  (const_formal_multilinear_series 𝕜 E v).radius = ⊤ :=
(const_formal_multilinear_series 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
  (by simp [const_formal_multilinear_series])

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `‖p n‖ rⁿ = o(aⁿ)`. -/
lemma is_o_of_lt_radius (h : ↑r < p.radius) :
  ∃ a ∈ Ioo (0 : ℝ) 1, (λ n, ‖p n‖ * r ^ n) =o[at_top] (pow a) :=
begin
  rw (tfae_exists_lt_is_o_pow (λ n, ‖p n‖ * r ^ n) 1).out 1 4,
  simp only [radius, lt_supr_iff] at h,
  rcases h with ⟨t, C, hC, rt⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at rt,
  have : 0 < (t : ℝ), from r.coe_nonneg.trans_lt rt,
  rw [← div_lt_one this] at rt,
  refine ⟨_, rt, C, or.inr zero_lt_one, λ n, _⟩,
  calc |‖p n‖ * r ^ n| = (‖p n‖ * t ^ n) * (r / t) ^ n :
    by field_simp [mul_right_comm, abs_mul, this.ne']
  ... ≤ C * (r / t) ^ n : mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (div_nonneg r.2 t.2) _)
end

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`. -/
lemma is_o_one_of_lt_radius (h : ↑r < p.radius) :
  (λ n, ‖p n‖ * r ^ n) =o[at_top] (λ _, 1 : ℕ → ℝ) :=
let ⟨a, ha, hp⟩ := p.is_o_of_lt_radius h in
hp.trans $ (is_o_pow_pow_of_lt_left ha.1.le ha.2).congr (λ n, rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `‖p n‖ * r ^ n ≤ C * a ^ n`. -/
lemma norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
  ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), ∀ n, ‖p n‖ * r^n ≤ C * a^n :=
begin
  rcases ((tfae_exists_lt_is_o_pow (λ n, ‖p n‖ * r ^ n) 1).out 1 5).mp (p.is_o_of_lt_radius h)
    with ⟨a, ha, C, hC, H⟩,
  exact ⟨a, ha, C, hC, λ n, (le_abs_self _).trans (H n)⟩
end

/-- If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
lemma lt_radius_of_is_O (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
  (hp : (λ n, ‖p n‖ * r ^ n) =O[at_top] (pow a)) :
  ↑r < p.radius :=
begin
  rcases ((tfae_exists_lt_is_o_pow (λ n, ‖p n‖ * r ^ n) 1).out 2 5).mp ⟨a, ha, hp⟩
    with ⟨a, ha, C, hC, hp⟩,
  rw [← pos_iff_ne_zero, ← nnreal.coe_pos] at h₀,
  lift a to ℝ≥0 using ha.1.le,
  have : (r : ℝ) < r / a :=
    by simpa only [div_one] using (div_lt_div_left h₀ zero_lt_one ha.1).2 ha.2,
  norm_cast at this,
  rw [← ennreal.coe_lt_coe] at this,
  refine this.trans_le (p.le_radius_of_bound C $ λ n, _),
  rw [nnreal.coe_div, div_pow, ← mul_div_assoc, div_le_iff (pow_pos ha.1 n)],
  exact (le_abs_self _).trans (hp n)
end

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
lemma norm_mul_pow_le_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ * r^n ≤ C :=
let ⟨a, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
in ⟨C, hC, λ n, (h n).trans $ mul_le_of_le_one_right hC.lt.le (pow_le_one _ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
lemma norm_le_div_pow_of_pos_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h0 : 0 < r) (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ ≤ C / r ^ n :=
let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h in
⟨C, hC, λ n, iff.mpr (le_div_iff (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
lemma nnnorm_mul_pow_le_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖₊ * r^n ≤ C :=
let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
in ⟨⟨C, hC.lt.le⟩, hC, by exact_mod_cast hp⟩

lemma le_radius_of_tendsto (p : formal_multilinear_series 𝕜 E F) {l : ℝ}
  (h : tendsto (λ n, ‖p n‖ * r^n) at_top (𝓝 l)) : ↑r ≤ p.radius :=
p.le_radius_of_is_O (h.is_O_one _)

lemma le_radius_of_summable_norm (p : formal_multilinear_series 𝕜 E F)
  (hs : summable (λ n, ‖p n‖ * r^n)) : ↑r ≤ p.radius :=
p.le_radius_of_tendsto hs.tendsto_at_top_zero

lemma not_summable_norm_of_radius_lt_nnnorm (p : formal_multilinear_series 𝕜 E F) {x : E}
  (h : p.radius < ‖x‖₊) : ¬ summable (λ n, ‖p n‖ * ‖x‖^n) :=
λ hs, not_le_of_lt h (p.le_radius_of_summable_norm hs)

lemma summable_norm_mul_pow (p : formal_multilinear_series 𝕜 E F)
  {r : ℝ≥0} (h : ↑r < p.radius) :
  summable (λ n : ℕ, ‖p n‖ * r ^ n) :=
begin
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h,
  exact summable_of_nonneg_of_le (λ n, mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)) hp
    ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _),
end

lemma summable_norm_apply (p : formal_multilinear_series 𝕜 E F)
  {x : E} (hx : x ∈ emetric.ball (0 : E) p.radius) :
  summable (λ n : ℕ, ‖p n (λ _, x)‖) :=
begin
  rw mem_emetric_ball_zero_iff at hx,
  refine summable_of_nonneg_of_le (λ _, norm_nonneg _) (λ n, ((p n).le_op_norm _).trans_eq _)
    (p.summable_norm_mul_pow hx),
  simp
end

lemma summable_nnnorm_mul_pow (p : formal_multilinear_series 𝕜 E F)
  {r : ℝ≥0} (h : ↑r < p.radius) :
  summable (λ n : ℕ, ‖p n‖₊ * r ^ n) :=
by { rw ← nnreal.summable_coe, push_cast, exact p.summable_norm_mul_pow h }

protected lemma summable [complete_space F]
  (p : formal_multilinear_series 𝕜 E F) {x : E} (hx : x ∈ emetric.ball (0 : E) p.radius) :
  summable (λ n : ℕ, p n (λ _, x)) :=
summable_of_summable_norm (p.summable_norm_apply hx)

lemma radius_eq_top_of_summable_norm (p : formal_multilinear_series 𝕜 E F)
  (hs : ∀ r : ℝ≥0, summable (λ n, ‖p n‖ * r^n)) : p.radius = ∞ :=
ennreal.eq_top_of_forall_nnreal_le (λ r, p.le_radius_of_summable_norm (hs r))

lemma radius_eq_top_iff_summable_norm (p : formal_multilinear_series 𝕜 E F) :
  p.radius = ∞ ↔ ∀ r : ℝ≥0, summable (λ n, ‖p n‖ * r^n) :=
begin
  split,
  { intros h r,
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ :=
      p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r:ℝ≥0∞) < p.radius, from h.symm ▸ ennreal.coe_lt_top),
    refine (summable_of_norm_bounded (λ n, (C : ℝ) * a ^ n)
      ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _) (λ n, _)),
    specialize hp n,
    rwa real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n)) },
  { exact p.radius_eq_top_of_summable_norm }
end

/-- If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically. -/
lemma le_mul_pow_of_radius_pos (p : formal_multilinear_series 𝕜 E F) (h : 0 < p.radius) :
  ∃ C r (hC : 0 < C) (hr : 0 < r), ∀ n, ‖p n‖ ≤ C * r ^ n :=
begin
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩,
  have rpos : 0 < (r : ℝ), by simp [ennreal.coe_pos.1 r0],
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩,
  refine ⟨C, r ⁻¹, Cpos, by simp [rpos], λ n, _⟩,
  convert hCp n,
  exact inv_pow _ _,
end

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
lemma min_radius_le_radius_add (p q : formal_multilinear_series 𝕜 E F) :
  min p.radius q.radius ≤ (p + q).radius :=
begin
  refine ennreal.le_of_forall_nnreal_lt (λ r hr, _),
  rw lt_min_iff at hr,
  have := ((p.is_o_one_of_lt_radius hr.1).add (q.is_o_one_of_lt_radius hr.2)).is_O,
  refine (p + q).le_radius_of_is_O ((is_O_of_le _ $ λ n, _).trans this),
  rw [← add_mul, norm_mul, norm_mul, norm_norm],
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)
end

@[simp] lemma radius_neg (p : formal_multilinear_series 𝕜 E F) : (-p).radius = p.radius :=
by simp [radius]

protected lemma has_sum [complete_space F]
  (p : formal_multilinear_series 𝕜 E F) {x : E} (hx : x ∈ emetric.ball (0 : E) p.radius) :
  has_sum (λ n : ℕ, p n (λ _, x)) (p.sum x) :=
(p.summable hx).has_sum

lemma radius_le_radius_continuous_linear_map_comp
  (p : formal_multilinear_series 𝕜 E F) (f : F →L[𝕜] G) :
  p.radius ≤ (f.comp_formal_multilinear_series p).radius :=
begin
  refine ennreal.le_of_forall_nnreal_lt (λ r hr, _),
  apply le_radius_of_is_O,
  apply (is_O.trans_is_o _ (p.is_o_one_of_lt_radius hr)).is_O,
  refine is_O.mul (@is_O_with.is_O _ _ _ _ _ (‖f‖) _ _ _ _) (is_O_refl _ _),
  apply is_O_with.of_bound (eventually_of_forall (λ n, _)),
  simpa only [norm_norm] using f.norm_comp_continuous_multilinear_map_le (p n)
end

end formal_multilinear_series

/-! ### Expanding a function as a power series -/
section

variables {f g : E → F} {p pf pg : formal_multilinear_series 𝕜 E F} {x : E} {r r' : ℝ≥0∞}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `‖y‖ < r`.
-/
structure has_fpower_series_on_ball
  (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) (r : ℝ≥0∞) : Prop :=
(r_le    : r ≤ p.radius)
(r_pos   : 0 < r)
(has_sum : ∀ {y}, y ∈ emetric.ball (0 : E) r → has_sum (λn:ℕ, p n (λ(i : fin n), y)) (f (x + y)))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def has_fpower_series_at (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) :=
∃ r, has_fpower_series_on_ball f p x r

variable (𝕜)
/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def analytic_at (f : E → F) (x : E) :=
∃ (p : formal_multilinear_series 𝕜 E F), has_fpower_series_at f p x

/-- Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is analytic around
every point of `s`. -/
def analytic_on (f : E → F) (s : set E) :=
∀ x, x ∈ s → analytic_at 𝕜 f x

variable {𝕜}

lemma has_fpower_series_on_ball.has_fpower_series_at (hf : has_fpower_series_on_ball f p x r) :
  has_fpower_series_at f p x := ⟨r, hf⟩

lemma has_fpower_series_at.analytic_at (hf : has_fpower_series_at f p x) : analytic_at 𝕜 f x :=
⟨p, hf⟩

lemma has_fpower_series_on_ball.analytic_at (hf : has_fpower_series_on_ball f p x r) :
  analytic_at 𝕜 f x :=
hf.has_fpower_series_at.analytic_at

lemma has_fpower_series_on_ball.congr (hf : has_fpower_series_on_ball f p x r)
  (hg : eq_on f g (emetric.ball x r)) :
  has_fpower_series_on_ball g p x r :=
{ r_le := hf.r_le,
  r_pos := hf.r_pos,
  has_sum := λ y hy,
  begin
    convert hf.has_sum hy,
    apply hg.symm,
    simpa [edist_eq_coe_nnnorm_sub] using hy,
  end }

/-- If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z - y)` has the
same power series around `x + y`. -/
lemma has_fpower_series_on_ball.comp_sub (hf : has_fpower_series_on_ball f p x r) (y : E) :
  has_fpower_series_on_ball (λ z, f (z - y)) p (x + y) r :=
{ r_le := hf.r_le,
  r_pos := hf.r_pos,
  has_sum := λ z hz, by { convert hf.has_sum hz, abel } }

lemma has_fpower_series_on_ball.has_sum_sub (hf : has_fpower_series_on_ball f p x r) {y : E}
  (hy : y ∈ emetric.ball x r) :
  has_sum (λ n : ℕ, p n (λ i, y - x)) (f y) :=
have y - x ∈ emetric.ball (0 : E) r, by simpa [edist_eq_coe_nnnorm_sub] using hy,
by simpa only [add_sub_cancel'_right] using hf.has_sum this

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

lemma has_fpower_series_at.congr (hf : has_fpower_series_at f p x) (hg : f =ᶠ[𝓝 x] g) :
  has_fpower_series_at g p x :=
begin
  rcases hf with ⟨r₁, h₁⟩,
  rcases emetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩,
  exact ⟨min r₁ r₂, (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
    (λ y hy, h₂ (emetric.ball_subset_ball inf_le_right hy))⟩
end

protected lemma has_fpower_series_at.eventually (hf : has_fpower_series_at f p x) :
  ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, has_fpower_series_on_ball f p x r :=
let ⟨r, hr⟩ := hf in
mem_of_superset (Ioo_mem_nhds_within_Ioi (left_mem_Ico.2 hr.r_pos)) $
  λ r' hr', hr.mono hr'.1 hr'.2.le

lemma has_fpower_series_on_ball.eventually_has_sum (hf : has_fpower_series_on_ball f p x r) :
  ∀ᶠ y in 𝓝 0, has_sum (λn:ℕ, p n (λ(i : fin n), y)) (f (x + y)) :=
by filter_upwards [emetric.ball_mem_nhds (0 : E) hf.r_pos] using λ _, hf.has_sum

lemma has_fpower_series_at.eventually_has_sum (hf : has_fpower_series_at f p x) :
  ∀ᶠ y in 𝓝 0, has_sum (λn:ℕ, p n (λ(i : fin n), y)) (f (x + y)) :=
let ⟨r, hr⟩ := hf in hr.eventually_has_sum

lemma has_fpower_series_on_ball.eventually_has_sum_sub (hf : has_fpower_series_on_ball f p x r) :
  ∀ᶠ y in 𝓝 x, has_sum (λn:ℕ, p n (λ(i : fin n), y - x)) (f y) :=
by filter_upwards [emetric.ball_mem_nhds x hf.r_pos] with y using hf.has_sum_sub

lemma has_fpower_series_at.eventually_has_sum_sub (hf : has_fpower_series_at f p x) :
  ∀ᶠ y in 𝓝 x, has_sum (λn:ℕ, p n (λ(i : fin n), y - x)) (f y) :=
let ⟨r, hr⟩ := hf in hr.eventually_has_sum_sub

lemma has_fpower_series_on_ball.eventually_eq_zero
  (hf : has_fpower_series_on_ball f (0 : formal_multilinear_series 𝕜 E F) x r) :
  ∀ᶠ z in 𝓝 x, f z = 0 :=
by filter_upwards [hf.eventually_has_sum_sub] with z hz using hz.unique has_sum_zero

lemma has_fpower_series_at.eventually_eq_zero
  (hf : has_fpower_series_at f (0 : formal_multilinear_series 𝕜 E F) x) :
  ∀ᶠ z in 𝓝 x, f z = 0 :=
let ⟨r, hr⟩ := hf in hr.eventually_eq_zero

lemma has_fpower_series_on_ball_const {c : F} {e : E} :
  has_fpower_series_on_ball (λ _, c) (const_formal_multilinear_series 𝕜 E c) e ⊤ :=
begin
  refine ⟨by simp, with_top.zero_lt_top, λ y hy, has_sum_single 0 (λ n hn, _)⟩,
  simp [const_formal_multilinear_series_apply hn]
end

lemma has_fpower_series_at_const {c : F} {e : E} :
  has_fpower_series_at (λ _, c) (const_formal_multilinear_series 𝕜 E c) e :=
⟨⊤, has_fpower_series_on_ball_const⟩

lemma analytic_at_const {v : F} : analytic_at 𝕜 (λ _, v) x :=
⟨const_formal_multilinear_series 𝕜 E v, has_fpower_series_at_const⟩

lemma analytic_on_const {v : F} {s : set E} : analytic_on 𝕜 (λ _, v) s :=
λ z _, analytic_at_const

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
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩,
  exact ⟨r, hr.1.add hr.2⟩
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
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma has_fpower_series_at.sub
  (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) :
  has_fpower_series_at (f - g) (pf - pg) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma analytic_at.sub (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) :
  analytic_at 𝕜 (f - g) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma analytic_on.mono {s t : set E} (hf : analytic_on 𝕜 f t) (hst : s ⊆ t) :
  analytic_on 𝕜 f s :=
λ z hz, hf z (hst hz)

lemma analytic_on.add {s : set E} (hf : analytic_on 𝕜 f s) (hg : analytic_on 𝕜 g s) :
  analytic_on 𝕜 (f + g) s :=
λ z hz, (hf z hz).add (hg z hz)

lemma analytic_on.sub {s : set E} (hf : analytic_on 𝕜 f s) (hg : analytic_on 𝕜 g s) :
  analytic_on 𝕜 (f - g) s :=
λ z hz, (hf z hz).sub (hg z hz)

lemma has_fpower_series_on_ball.coeff_zero (hf : has_fpower_series_on_ball f pf x r)
  (v : fin 0 → E) : pf 0 v = f x :=
begin
  have v_eq : v = (λ i, 0) := subsingleton.elim _ _,
  have zero_mem : (0 : E) ∈ emetric.ball (0 : E) r, by simp [hf.r_pos],
  have : ∀ i ≠ 0, pf i (λ j, 0) = 0,
  { assume i hi,
    have : 0 < i := pos_iff_ne_zero.2 hi,
    exact continuous_multilinear_map.map_coord_zero _ (⟨0, this⟩ : fin i) rfl },
  have A := (hf.has_sum zero_mem).unique (has_sum_single _ this),
  simpa [v_eq] using A.symm,
end

lemma has_fpower_series_at.coeff_zero (hf : has_fpower_series_at f pf x) (v : fin 0 → E) :
  pf 0 v = f x :=
let ⟨rf, hrf⟩ := hf in hrf.coeff_zero v

/-- If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ f` has the
power series `g ∘ p` on the same ball. -/
lemma _root_.continuous_linear_map.comp_has_fpower_series_on_ball
  (g : F →L[𝕜] G) (h : has_fpower_series_on_ball f p x r) :
  has_fpower_series_on_ball (g ∘ f) (g.comp_formal_multilinear_series p) x r :=
{ r_le := h.r_le.trans (p.radius_le_radius_continuous_linear_map_comp _),
  r_pos := h.r_pos,
  has_sum := λ y hy, by simpa only [continuous_linear_map.comp_formal_multilinear_series_apply,
      continuous_linear_map.comp_continuous_multilinear_map_coe, function.comp_app]
    using g.has_sum (h.has_sum hy) }

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
lemma _root_.continuous_linear_map.comp_analytic_on {s : set E}
  (g : F →L[𝕜] G) (h : analytic_on 𝕜 f s) :
  analytic_on 𝕜 (g ∘ f) s :=
begin
  rintros x hx,
  rcases h x hx with ⟨p, r, hp⟩,
  exact ⟨g.comp_formal_multilinear_series p, r, g.comp_has_fpower_series_on_ball hp⟩,
end

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
lemma has_fpower_series_on_ball.uniform_geometric_approx' {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ℝ≥0∞) < r) :
  ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), (∀ y ∈ metric.ball (0 : E) r', ∀ n,
    ‖f (x + y) - p.partial_sum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n) :=
begin
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), ∀ n, ‖p n‖ * r' ^n ≤ C * a^n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le),
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), λ y hy n, _⟩,
  have yr' : ‖y‖ < r', by { rw ball_zero_eq at hy, exact hy },
  have hr'0 : 0 < (r' : ℝ), from (norm_nonneg _).trans_lt yr',
  have : y ∈ emetric.ball (0 : E) r,
  { refine mem_emetric_ball_zero_iff.2 (lt_trans _ h),
    exact_mod_cast yr' },
  rw [norm_sub_rev, ← mul_div_right_comm],
  have ya : a * (‖y‖ / ↑r') ≤ a,
    from mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg),
  suffices : ‖p.partial_sum n y - f (x + y)‖ ≤ C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')),
  { refine this.trans _,
    apply_rules [div_le_div_of_le_left, sub_pos.2, div_nonneg, mul_nonneg, pow_nonneg, hC.lt.le,
      ha.1.le, norm_nonneg, nnreal.coe_nonneg, ha.2, (sub_le_sub_iff_left _).2]; apply_instance },
  apply norm_sub_le_of_geometric_bound_of_has_sum (ya.trans_lt ha.2) _ (hf.has_sum this),
  assume n,
  calc ‖(p n) (λ (i : fin n), y)‖ ≤ ‖p n‖ * (∏ i : fin n, ‖y‖) :
      continuous_multilinear_map.le_op_norm _ _
    ... = (‖p n‖ * r' ^ n) * (‖y‖ / r') ^ n : by field_simp [hr'0.ne', mul_right_comm]
    ... ≤ (C * a ^ n) * (‖y‖ / r') ^ n :
      mul_le_mul_of_nonneg_right (hp n) (pow_nonneg (div_nonneg (norm_nonneg _) r'.coe_nonneg) _)
    ... ≤ C * (a * (‖y‖ / r')) ^ n : by rw [mul_pow, mul_assoc]
end

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
lemma has_fpower_series_on_ball.uniform_geometric_approx {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ℝ≥0∞) < r) :
  ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), (∀ y ∈ metric.ball (0 : E) r', ∀ n,
    ‖f (x + y) - p.partial_sum n y‖ ≤ C * a ^ n) :=
begin
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0),
    (∀ y ∈ metric.ball (0 : E) r', ∀ n, ‖f (x + y) - p.partial_sum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n),
    from hf.uniform_geometric_approx' h,
  refine ⟨a, ha, C, hC, λ y hy n, (hp y hy n).trans _⟩,
  have yr' : ‖y‖ < r', by rwa ball_zero_eq at hy,
  refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ _ _) hC.lt.le,
  exacts [mul_nonneg ha.1.le (div_nonneg (norm_nonneg y) r'.coe_nonneg),
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)]
end

/-- Taylor formula for an analytic function, `is_O` version. -/
lemma has_fpower_series_at.is_O_sub_partial_sum_pow (hf : has_fpower_series_at f p x) (n : ℕ) :
  (λ y : E, f (x + y) - p.partial_sum n y) =O[𝓝 0] (λ y, ‖y‖ ^ n) :=
begin
  rcases hf with ⟨r, hf⟩,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩,
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0),
    (∀ y ∈ metric.ball (0 : E) r', ∀ n, ‖f (x + y) - p.partial_sum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n),
    from hf.uniform_geometric_approx' h,
  refine is_O_iff.2 ⟨C * (a / r') ^ n, _⟩,
  replace r'0 : 0 < (r' : ℝ), by exact_mod_cast r'0,
  filter_upwards [metric.ball_mem_nhds (0 : E) r'0] with y hy,
  simpa [mul_pow, mul_div_assoc, mul_assoc, div_mul_eq_mul_div] using hp y hy n,
end

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
lemma has_fpower_series_on_ball.is_O_image_sub_image_sub_deriv_principal
  (hf : has_fpower_series_on_ball f p x r) (hr : r' < r) :
  (λ y : E × E, f y.1 - f y.2 - (p 1 (λ _, y.1 - y.2))) =O[𝓟 (emetric.ball (x, x) r')]
    (λ y, ‖y - (x, x)‖ * ‖y.1 - y.2‖) :=
begin
  lift r' to ℝ≥0 using ne_top_of_lt hr,
  rcases (zero_le r').eq_or_lt with rfl|hr'0,
  { simp only [is_O_bot, emetric.ball_zero, principal_empty, ennreal.coe_zero] },
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
    ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), ∀ (n : ℕ), ‖p n‖ * ↑r' ^ n ≤ C * a ^ n,
    from p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le),
  simp only [← le_div_iff (pow_pos (nnreal.coe_pos.2 hr'0) _)] at hp,
  set L : E × E → ℝ := λ y,
    (C * (a / r') ^ 2) * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a)),
  have hL : ∀ y ∈ emetric.ball (x, x) r',
    ‖f y.1 - f y.2 - (p 1 (λ _, y.1 - y.2))‖ ≤ L y,
  { intros y hy',
    have hy : y ∈ emetric.ball x r ×ˢ emetric.ball x r,
    { rw [emetric.ball_prod_same], exact emetric.ball_subset_ball hr.le hy' },
    set A : ℕ → F := λ n, p n (λ _, y.1 - x) - p n (λ _, y.2 - x),
    have hA : has_sum (λ n, A (n + 2)) (f y.1 - f y.2 - (p 1 (λ _, y.1 - y.2))),
    { convert (has_sum_nat_add_iff' 2).2 ((hf.has_sum_sub hy.1).sub (hf.has_sum_sub hy.2)) using 1,
      rw [finset.sum_range_succ, finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self,
        zero_add, ← subsingleton.pi_single_eq (0 : fin 1) (y.1 - x), pi.single,
        ← subsingleton.pi_single_eq (0 : fin 1) (y.2 - x), pi.single, ← (p 1).map_sub, ← pi.single,
        subsingleton.pi_single_eq, sub_sub_sub_cancel_right] },
    rw [emetric.mem_ball, edist_eq_coe_nnnorm_sub, ennreal.coe_lt_coe] at hy',
    set B : ℕ → ℝ := λ n,
      (C * (a / r') ^ 2) * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n),
    have hAB : ∀ n, ‖A (n + 2)‖ ≤ B n := λ n,
    calc ‖A (n + 2)‖ ≤ ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ :
      by simpa only [fintype.card_fin, pi_norm_const (_ : E), prod.norm_def, pi.sub_def,
        prod.fst_sub, prod.snd_sub, sub_sub_sub_cancel_right]
        using (p $ n + 2).norm_image_sub_le (λ _, y.1 - x) (λ _, y.2 - x)
    ... = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) :
      by { rw [pow_succ ‖y - (x, x)‖], ring }
    ... ≤ (C * a ^ (n + 2) / r' ^ (n + 2)) * r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) :
      by apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul, hp, pow_le_pow_of_le_left,
        hy'.le, norm_nonneg, pow_nonneg, div_nonneg, mul_nonneg, nat.cast_nonneg,
        hC.le, r'.coe_nonneg, ha.1.le]
    ... = B n :
      by { field_simp [B, pow_succ, hr'0.ne'], simp only [mul_assoc, mul_comm, mul_left_comm] },
    have hBL : has_sum B (L y),
    { apply has_sum.mul_left,
      simp only [add_mul],
      have : ‖a‖ < 1, by simp only [real.norm_eq_abs, abs_of_pos ha.1, ha.2],
      convert (has_sum_coe_mul_geometric_of_norm_lt_1 this).add
        ((has_sum_geometric_of_norm_lt_1 this).mul_left 2) },
    exact hA.norm_le_of_bounded hBL hAB },
  suffices : L =O[𝓟 (emetric.ball (x, x) r')] (λ y, ‖y - (x, x)‖ * ‖y.1 - y.2‖),
  { refine (is_O.of_bound 1 (eventually_principal.2 $ λ y hy, _)).trans this,
    rw one_mul,
    exact (hL y hy).trans (le_abs_self _) },
  simp_rw [L, mul_right_comm _ (_ * _)],
  exact (is_O_refl _ _).const_mul_left _,
end

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
lemma has_fpower_series_on_ball.image_sub_sub_deriv_le
  (hf : has_fpower_series_on_ball f p x r) (hr : r' < r) :
  ∃ C, ∀ (y z ∈ emetric.ball x r'),
    ‖f y - f z - (p 1 (λ _, y - z))‖ ≤ C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖ :=
by simpa only [is_O_principal, mul_assoc, norm_mul, norm_norm, prod.forall,
  emetric.mem_ball, prod.edist_eq, max_lt_iff, and_imp, @forall_swap (_ < _) E]
  using hf.is_O_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
lemma has_fpower_series_at.is_O_image_sub_norm_mul_norm_sub (hf : has_fpower_series_at f p x) :
  (λ y : E × E, f y.1 - f y.2 - (p 1 (λ _, y.1 - y.2))) =O[𝓝 (x, x)]
    (λ y, ‖y - (x, x)‖ * ‖y.1 - y.2‖) :=
begin
  rcases hf with ⟨r, hf⟩,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩,
  refine (hf.is_O_image_sub_image_sub_deriv_principal h).mono _,
  exact le_principal_iff.2 (emetric.ball_mem_nhds _ r'0)
end

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
lemma has_fpower_series_on_ball.tendsto_uniformly_on {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ℝ≥0∞) < r) :
  tendsto_uniformly_on (λ n y, p.partial_sum n y)
    (λ y, f (x + y)) at_top (metric.ball (0 : E) r') :=
begin
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0),
    (∀ y ∈ metric.ball (0 : E) r', ∀ n, ‖f (x + y) - p.partial_sum n y‖ ≤ C * a ^ n),
    from hf.uniform_geometric_approx h,
  refine metric.tendsto_uniformly_on_iff.2 (λ ε εpos, _),
  have L : tendsto (λ n, (C : ℝ) * a^n) at_top (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 ha.1.le ha.2),
  rw mul_zero at L,
  refine (L.eventually (gt_mem_nhds εpos)).mono (λ n hn y hy, _),
  rw dist_eq_norm,
  exact (hp y hy n).trans_lt hn
end

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
lemma has_fpower_series_on_ball.tendsto_locally_uniformly_on
  (hf : has_fpower_series_on_ball f p x r) :
  tendsto_locally_uniformly_on (λ n y, p.partial_sum n y) (λ y, f (x + y))
    at_top (emetric.ball (0 : E) r) :=
begin
  assume u hu x hx,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hx with ⟨r', xr', hr'⟩,
  have : emetric.ball (0 : E) r' ∈ 𝓝 x :=
    is_open.mem_nhds emetric.is_open_ball xr',
  refine ⟨emetric.ball (0 : E) r', mem_nhds_within_of_mem_nhds this, _⟩,
  simpa [metric.emetric_ball_nnreal] using hf.tendsto_uniformly_on hr' u hu
end

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
lemma has_fpower_series_on_ball.tendsto_uniformly_on' {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ℝ≥0∞) < r) :
  tendsto_uniformly_on (λ n y, p.partial_sum n (y - x)) f at_top (metric.ball (x : E) r') :=
begin
  convert (hf.tendsto_uniformly_on h).comp (λ y, y - x),
  { simp [(∘)] },
  { ext z, simp [dist_eq_norm] }
end

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
lemma has_fpower_series_on_ball.tendsto_locally_uniformly_on'
  (hf : has_fpower_series_on_ball f p x r) :
  tendsto_locally_uniformly_on (λ n y, p.partial_sum n (y - x)) f at_top (emetric.ball (x : E) r) :=
begin
  have A : continuous_on (λ (y : E), y - x) (emetric.ball (x : E) r) :=
    (continuous_id.sub continuous_const).continuous_on,
  convert (hf.tendsto_locally_uniformly_on).comp (λ (y : E), y - x) _ A,
  { ext z, simp },
  { assume z, simp [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub] }
end

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
protected lemma has_fpower_series_on_ball.continuous_on
  (hf : has_fpower_series_on_ball f p x r) : continuous_on f (emetric.ball x r) :=
hf.tendsto_locally_uniformly_on'.continuous_on $ eventually_of_forall $ λ n,
  ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).continuous_on

protected lemma has_fpower_series_at.continuous_at (hf : has_fpower_series_at f p x) :
  continuous_at f x :=
let ⟨r, hr⟩ := hf in hr.continuous_on.continuous_at (emetric.ball_mem_nhds x (hr.r_pos))

protected lemma analytic_at.continuous_at (hf : analytic_at 𝕜 f x) : continuous_at f x :=
let ⟨p, hp⟩ := hf in hp.continuous_at

protected lemma analytic_on.continuous_on {s : set E} (hf : analytic_on 𝕜 f s) :
  continuous_on f s :=
λ x hx, (hf x hx).continuous_at.continuous_within_at

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected lemma formal_multilinear_series.has_fpower_series_on_ball [complete_space F]
  (p : formal_multilinear_series 𝕜 E F) (h : 0 < p.radius) :
  has_fpower_series_on_ball p.sum p 0 p.radius :=
{ r_le    := le_rfl,
  r_pos   := h,
  has_sum := λ y hy, by { rw zero_add, exact p.has_sum hy } }

lemma has_fpower_series_on_ball.sum (h : has_fpower_series_on_ball f p x r)
  {y : E} (hy : y ∈ emetric.ball (0 : E) r) : f (x + y) = p.sum y :=
(h.has_sum hy).tsum_eq.symm

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected lemma formal_multilinear_series.continuous_on [complete_space F] :
  continuous_on p.sum (emetric.ball 0 p.radius) :=
begin
  cases (zero_le p.radius).eq_or_lt with h h,
  { simp [← h, continuous_on_empty] },
  { exact (p.has_fpower_series_on_ball h).continuous_on }
end

end

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`,  `p₁ n (λ i, y) = p₂ n (λ i, y)`. In the one-dimensional case, when
`f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`formal_multilinear_series.mk_pi_field`, and hence are determined completely by the value of
`p₁ n (λ i, 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/

section uniqueness

open continuous_multilinear_map

lemma asymptotics.is_O.continuous_multilinear_map_apply_eq_zero {n : ℕ} {p : E [×n]→L[𝕜] F}
  (h : (λ y, p (λ i, y)) =O[𝓝 0] (λ y, ‖y‖ ^ (n + 1))) (y : E) :
  p (λ i, y) = 0 :=
begin
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos,
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (is_O_with_iff.mp hc),
  obtain ⟨δ, δ_pos, δε⟩ := (metric.is_open_iff.mp t_open) 0 z_mem,
  clear h hc z_mem,
  cases n,
  { exact norm_eq_zero.mp (by simpa only [fin0_apply_norm, norm_eq_zero, norm_zero, zero_pow',
      ne.def, nat.one_ne_zero, not_false_iff, mul_zero, norm_le_zero_iff]
      using ht 0 (δε (metric.mem_ball_self δ_pos))), },
  { refine or.elim (em (y = 0)) (λ hy, by simpa only [hy] using p.map_zero) (λ hy, _),
    replace hy := norm_pos_iff.mpr hy,
    refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add (λ ε ε_pos, _)) (norm_nonneg _)),
    have h₀ := mul_pos c_pos (pow_pos hy (n.succ + 1)),
    obtain ⟨k, k_pos, k_norm⟩ := normed_field.exists_norm_lt 𝕜
      (lt_min (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀))),
    have h₁ : ‖k • y‖ < δ,
    { rw norm_smul,
      exact inv_mul_cancel_right₀ hy.ne.symm δ ▸ mul_lt_mul_of_pos_right
        (lt_of_lt_of_le k_norm (min_le_left _ _)) hy },
    have h₂ := calc
      ‖p (λ i, k • y)‖ ≤ c * ‖k • y‖ ^ (n.succ + 1)
                       : by simpa only [norm_pow, norm_norm]
                           using ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
      ...              = ‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))
                       : by { simp only [norm_smul, mul_pow], rw pow_succ, ring },
    have h₃ : ‖k‖ * (c * ‖y‖ ^ (n.succ + 1)) < ε, from inv_mul_cancel_right₀ h₀.ne.symm ε ▸
      mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_right _ _)) h₀,
    calc ‖p (λ i, y)‖ = ‖(k⁻¹) ^ n.succ‖ * ‖p (λ i, k • y)‖
        : by simpa only [inv_smul_smul₀ (norm_pos_iff.mp k_pos),
            norm_smul, finset.prod_const, finset.card_fin] using
            congr_arg norm (p.map_smul_univ (λ (i : fin n.succ), k⁻¹) (λ (i : fin n.succ), k • y))
    ...              ≤ ‖(k⁻¹) ^ n.succ‖ * (‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))))
        : mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
    ...              = ‖(k⁻¹ * k) ^ n.succ‖ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))
        : by { rw ←mul_assoc, simp [norm_mul, mul_pow] }
    ...              ≤ 0 + ε
        : by { rw inv_mul_cancel (norm_pos_iff.mp k_pos), simpa using h₃.le }, },
end

/-- If a formal multilinear series `p` represents the zero function at `x : E`, then the
terms `p n (λ i, y)` appearing the in sum are zero for any `n : ℕ`, `y : E`. -/
lemma has_fpower_series_at.apply_eq_zero {p : formal_multilinear_series 𝕜 E F} {x : E}
  (h : has_fpower_series_at 0 p x) (n : ℕ) :
  ∀ y : E, p n (λ i, y) = 0 :=
begin
  refine nat.strong_rec_on n (λ k hk, _),
  have psum_eq : p.partial_sum (k + 1) = (λ y, p k (λ i, y)),
  { funext z,
    refine finset.sum_eq_single _ (λ b hb hnb, _) (λ hn, _),
    { have := finset.mem_range_succ_iff.mp hb,
      simp only [hk b (this.lt_of_ne hnb), pi.zero_apply, zero_apply] },
    { exact false.elim (hn (finset.mem_range.mpr (lt_add_one k))) } },
  replace h := h.is_O_sub_partial_sum_pow k.succ,
  simp only [psum_eq, zero_sub, pi.zero_apply, asymptotics.is_O_neg_left] at h,
  exact h.continuous_multilinear_map_apply_eq_zero,
end

/-- A one-dimensional formal multilinear series representing the zero function is zero. -/
lemma has_fpower_series_at.eq_zero {p : formal_multilinear_series 𝕜 𝕜 E} {x : 𝕜}
  (h : has_fpower_series_at 0 p x) : p = 0 :=
by { ext n x, rw ←mk_pi_field_apply_one_eq_self (p n), simp [h.apply_eq_zero n 1] }

/-- One-dimensional formal multilinear series representing the same function are equal. -/
theorem has_fpower_series_at.eq_formal_multilinear_series
  {p₁ p₂ : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E} {x : 𝕜}
  (h₁ : has_fpower_series_at f p₁ x) (h₂ : has_fpower_series_at f p₂ x) :
  p₁ = p₂ :=
sub_eq_zero.mp (has_fpower_series_at.eq_zero (by simpa only [sub_self] using h₁.sub h₂))

lemma has_fpower_series_at.eq_formal_multilinear_series_of_eventually
  {p q : formal_multilinear_series 𝕜 𝕜 E} {f g : 𝕜 → E} {x : 𝕜} (hp : has_fpower_series_at f p x)
  (hq : has_fpower_series_at g q x) (heq : ∀ᶠ z in 𝓝 x, f z = g z) :
  p = q :=
(hp.congr heq).eq_formal_multilinear_series hq

/-- A one-dimensional formal multilinear series representing a locally zero function is zero. -/
lemma has_fpower_series_at.eq_zero_of_eventually {p : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E}
  {x : 𝕜} (hp : has_fpower_series_at f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0 :=
(hp.congr hf).eq_zero

/-- If a function `f : 𝕜 → E` has two power series representations at `x`, then the given radii in
which convergence is guaranteed may be interchanged. This can be useful when the formal multilinear
series in one representation has a particularly nice form, but the other has a larger radius. -/
theorem has_fpower_series_on_ball.exchange_radius
  {p₁ p₂ : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E} {r₁ r₂ : ℝ≥0∞} {x : 𝕜}
  (h₁ : has_fpower_series_on_ball f p₁ x r₁) (h₂ : has_fpower_series_on_ball f p₂ x r₂) :
  has_fpower_series_on_ball f p₁ x r₂ :=
h₂.has_fpower_series_at.eq_formal_multilinear_series h₁.has_fpower_series_at ▸ h₂

/-- If a function `f : 𝕜 → E` has power series representation `p` on a ball of some radius and for
each positive radius it has some power series representation, then `p` converges to `f` on the whole
`𝕜`. -/
theorem has_fpower_series_on_ball.r_eq_top_of_exists {f : 𝕜 → E} {r : ℝ≥0∞} {x : 𝕜}
  {p : formal_multilinear_series 𝕜 𝕜 E} (h : has_fpower_series_on_ball f p x r)
  (h' : ∀ (r' : ℝ≥0) (hr : 0 < r'),
    ∃ p' : formal_multilinear_series 𝕜 𝕜 E, has_fpower_series_on_ball f p' x r') :
  has_fpower_series_on_ball f p x ∞ :=
{ r_le := ennreal.le_of_forall_pos_nnreal_lt $ λ r hr hr',
    let ⟨p', hp'⟩ := h' r hr in (h.exchange_radius hp').r_le,
  r_pos := ennreal.coe_lt_top,
  has_sum := λ y hy, let ⟨r', hr'⟩ := exists_gt ‖y‖₊, ⟨p', hp'⟩ := h' r' hr'.ne_bot.bot_lt
    in (h.exchange_radius hp').has_sum $ mem_emetric_ball_zero_iff.mpr (ennreal.coe_lt_coe.2 hr') }

end uniqueness

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/

namespace formal_multilinear_series

section

variables (p : formal_multilinear_series 𝕜 E F) {x y : E} {r R : ℝ≥0}

/-- A term of `formal_multilinear_series.change_origin_series`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Each term of `p.change_origin x`
is itself an analytic function of `x` given by the series `p.change_origin_series`. Each term in
`change_origin_series` is the sum of `change_origin_series_term`'s over all `s` of cardinality `l`.
The definition is such that
`p.change_origin_series_term k l s hs (λ _, x) (λ _, y) = p (k + l) (s.piecewise (λ _, x) (λ _, y))`
-/
def change_origin_series_term (k l : ℕ) (s : finset (fin (k + l))) (hs : s.card = l) :
  E [×l]→L[𝕜] E [×k]→L[𝕜] F :=
continuous_multilinear_map.curry_fin_finset 𝕜 E F hs
    (by erw [finset.card_compl, fintype.card_fin, hs, add_tsub_cancel_right]) (p $ k + l)

lemma change_origin_series_term_apply (k l : ℕ) (s : finset (fin (k + l))) (hs : s.card = l)
  (x y : E) :
  p.change_origin_series_term k l s hs (λ _, x) (λ _, y) =
    p (k + l) (s.piecewise (λ _, x) (λ _, y)) :=
continuous_multilinear_map.curry_fin_finset_apply_const _ _ _ _ _

@[simp] lemma norm_change_origin_series_term (k l : ℕ) (s : finset (fin (k + l)))
  (hs : s.card = l) :
  ‖p.change_origin_series_term k l s hs‖ = ‖p (k + l)‖ :=
by simp only [change_origin_series_term, linear_isometry_equiv.norm_map]

@[simp] lemma nnnorm_change_origin_series_term (k l : ℕ) (s : finset (fin (k + l)))
  (hs : s.card = l) :
  ‖p.change_origin_series_term k l s hs‖₊ = ‖p (k + l)‖₊ :=
by simp only [change_origin_series_term, linear_isometry_equiv.nnnorm_map]

lemma nnnorm_change_origin_series_term_apply_le (k l : ℕ) (s : finset (fin (k + l)))
  (hs : s.card = l) (x y : E) :
  ‖p.change_origin_series_term k l s hs (λ _, x) (λ _, y)‖₊ ≤ ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k :=
begin
  rw [← p.nnnorm_change_origin_series_term k l s hs, ← fin.prod_const, ← fin.prod_const],
  apply continuous_multilinear_map.le_of_op_nnnorm_le,
  apply continuous_multilinear_map.le_op_nnnorm
end

/-- The power series for `f.change_origin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Its `k`-th term is the sum of
the series `p.change_origin_series k`. -/
def change_origin_series (k : ℕ) : formal_multilinear_series 𝕜 E (E [×k]→L[𝕜] F) :=
λ l, ∑ s : {s : finset (fin (k + l)) // finset.card s = l}, p.change_origin_series_term k l s s.2

lemma nnnorm_change_origin_series_le_tsum (k l : ℕ) :
  ‖p.change_origin_series k l‖₊ ≤
    ∑' (x : {s : finset (fin (k + l)) // s.card = l}), ‖p (k + l)‖₊ :=
(nnnorm_sum_le _ _).trans_eq $ by simp only [tsum_fintype, nnnorm_change_origin_series_term]

lemma nnnorm_change_origin_series_apply_le_tsum (k l : ℕ) (x : E) :
  ‖p.change_origin_series k l (λ _, x)‖₊ ≤
    ∑' s : {s : finset (fin (k + l)) // s.card = l}, ‖p (k + l)‖₊ * ‖x‖₊ ^ l :=
begin
  rw [nnreal.tsum_mul_right, ← fin.prod_const],
  exact (p.change_origin_series k l).le_of_op_nnnorm_le _
    (p.nnnorm_change_origin_series_le_tsum _ _)
end

/--
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.
-/
def change_origin (x : E) : formal_multilinear_series 𝕜 E F :=
λ k, (p.change_origin_series k).sum x

/-- An auxiliary equivalence useful in the proofs about
`formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a
`finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`finset (fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps] def change_origin_index_equiv :
  (Σ k l : ℕ, {s : finset (fin (k + l)) // s.card = l}) ≃ Σ n : ℕ, finset (fin n) :=
{ to_fun := λ s, ⟨s.1 + s.2.1, s.2.2⟩,
  inv_fun := λ s, ⟨s.1 - s.2.card, s.2.card, ⟨s.2.map
    (fin.cast $ (tsub_add_cancel_of_le $ card_finset_fin_le s.2).symm).to_equiv.to_embedding,
    finset.card_map _⟩⟩,
  left_inv :=
    begin
      rintro ⟨k, l, ⟨s : finset (fin $ k + l), hs : s.card = l⟩⟩,
      dsimp only [subtype.coe_mk],
      -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
      -- formulate the generalized goal
      suffices : ∀ k' l', k' = k → l' = l → ∀ (hkl : k + l = k' + l') hs',
        (⟨k', l', ⟨finset.map (fin.cast hkl).to_equiv.to_embedding s, hs'⟩⟩ :
          (Σ k l : ℕ, {s : finset (fin (k + l)) // s.card = l})) = ⟨k, l, ⟨s, hs⟩⟩,
      { apply this; simp only [hs, add_tsub_cancel_right] },
      rintro _ _ rfl rfl hkl hs',
      simp only [equiv.refl_to_embedding, fin.cast_refl, finset.map_refl, eq_self_iff_true,
        order_iso.refl_to_equiv, and_self, heq_iff_eq]
    end,
  right_inv :=
    begin
      rintro ⟨n, s⟩,
      simp [tsub_add_cancel_of_le (card_finset_fin_le s), fin.cast_to_equiv]
    end }

lemma change_origin_series_summable_aux₁ {r r' : ℝ≥0} (hr : (r + r' : ℝ≥0∞) < p.radius) :
  summable (λ s : Σ k l : ℕ, {s : finset (fin (k + l)) // s.card = l},
    ‖p (s.1 + s.2.1)‖₊ * r ^ s.2.1 * r' ^ s.1) :=
begin
  rw ← change_origin_index_equiv.symm.summable_iff,
  dsimp only [(∘), change_origin_index_equiv_symm_apply_fst,
    change_origin_index_equiv_symm_apply_snd_fst],
  have : ∀ n : ℕ, has_sum
    (λ s : finset (fin n), ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
    (‖p n‖₊ * (r + r') ^ n),
  { intro n,
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to has_sum (λ s : finset (fin n), ‖p n‖₊ * (r ^ s.card * r' ^ (n - s.card))) _,
    { ext1 s, rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc] },
    rw ← fin.sum_pow_mul_eq_add_pow,
    exact (has_sum_fintype _).mul_left _ },
  refine nnreal.summable_sigma.2 ⟨λ n, (this n).summable, _⟩,
  simp only [(this _).tsum_eq],
  exact p.summable_nnnorm_mul_pow hr
end

lemma change_origin_series_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
  summable (λ s : Σ l : ℕ, {s : finset (fin (k + l)) // s.card = l}, ‖p (k + s.1)‖₊ * r ^ s.1) :=
begin
  rcases ennreal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩,
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne']
    using ((nnreal.summable_sigma.1
      (p.change_origin_series_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹
end

lemma change_origin_series_summable_aux₃ {r : ℝ≥0} (hr : ↑r < p.radius) (k : ℕ) :
  summable (λ l : ℕ, ‖p.change_origin_series k l‖₊ * r ^ l) :=
begin
  refine nnreal.summable_of_le (λ n, _)
    (nnreal.summable_sigma.1 $ p.change_origin_series_summable_aux₂ hr k).2,
  simp only [nnreal.tsum_mul_right],
  exact mul_le_mul' (p.nnnorm_change_origin_series_le_tsum _ _) le_rfl
end

lemma le_change_origin_series_radius (k : ℕ) :
  p.radius ≤ (p.change_origin_series k).radius :=
ennreal.le_of_forall_nnreal_lt $ λ r hr,
  le_radius_of_summable_nnnorm _ (p.change_origin_series_summable_aux₃ hr k)

lemma nnnorm_change_origin_le (k : ℕ) (h : (‖x‖₊ : ℝ≥0∞) < p.radius) :
  ‖p.change_origin x k‖₊ ≤
    ∑' s : Σ l : ℕ, {s : finset (fin (k + l)) // s.card = l}, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1 :=
begin
  refine tsum_of_nnnorm_bounded _ (λ l, p.nnnorm_change_origin_series_apply_le_tsum k l x),
  have := p.change_origin_series_summable_aux₂ h k,
  refine has_sum.sigma this.has_sum (λ l, _),
  exact ((nnreal.summable_sigma.1 this).1 l).has_sum
end

/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ‖x‖`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
lemma change_origin_radius : p.radius - ‖x‖₊ ≤ (p.change_origin x).radius :=
begin
  refine ennreal.le_of_forall_pos_nnreal_lt (λ r h0 hr, _),
  rw [lt_tsub_iff_right, add_comm] at hr,
  have hr' : (‖x‖₊ : ℝ≥0∞) < p.radius, from (le_add_right le_rfl).trans_lt hr,
  apply le_radius_of_summable_nnnorm,
  have : ∀ k : ℕ, ‖p.change_origin x k‖₊ * r ^ k ≤
    (∑' s : Σ l : ℕ, {s : finset (fin (k + l)) // s.card = l}, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1) * r ^ k,
    from λ k, mul_le_mul_right' (p.nnnorm_change_origin_le k hr') (r ^ k),
  refine nnreal.summable_of_le this _,
  simpa only [← nnreal.tsum_mul_right]
    using (nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr)).2
end

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variables [complete_space F] (p : formal_multilinear_series 𝕜 E F) {x y : E} {r R : ℝ≥0}

lemma has_fpower_series_on_ball_change_origin (k : ℕ) (hr : 0 < p.radius) :
  has_fpower_series_on_ball (λ x, p.change_origin x k) (p.change_origin_series k) 0 p.radius :=
have _ := p.le_change_origin_series_radius k,
((p.change_origin_series k).has_fpower_series_on_ball (hr.trans_le this)).mono hr this

/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem change_origin_eval (h : (‖x‖₊ + ‖y‖₊ : ℝ≥0∞) < p.radius) :
  (p.change_origin x).sum y = (p.sum (x + y)) :=
begin
  have radius_pos : 0 < p.radius := lt_of_le_of_lt (zero_le _) h,
  have x_mem_ball : x ∈ emetric.ball (0 : E) p.radius,
    from mem_emetric_ball_zero_iff.2 ((le_add_right le_rfl).trans_lt h),
  have y_mem_ball : y ∈ emetric.ball (0 : E) (p.change_origin x).radius,
  { refine mem_emetric_ball_zero_iff.2 (lt_of_lt_of_le _ p.change_origin_radius),
    rwa [lt_tsub_iff_right, add_comm] },
  have x_add_y_mem_ball : x + y ∈ emetric.ball (0 : E) p.radius,
  { refine mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt _ h),
    exact_mod_cast nnnorm_add_le x y },
  set f : (Σ (k l : ℕ), {s : finset (fin (k + l)) // s.card = l}) → F :=
    λ s, p.change_origin_series_term s.1 s.2.1 s.2.2 s.2.2.2 (λ _, x) (λ _, y),
  have hsf : summable f,
  { refine summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₁ h) _,
    rintro ⟨k, l, s, hs⟩, dsimp only [subtype.coe_mk],
    exact p.nnnorm_change_origin_series_term_apply_le _ _ _ _ _ _ },
  have hf : has_sum f ((p.change_origin x).sum y),
  { refine has_sum.sigma_of_has_sum ((p.change_origin x).summable y_mem_ball).has_sum (λ k, _) hsf,
    { dsimp only [f],
      refine continuous_multilinear_map.has_sum_eval _ _,
      have := (p.has_fpower_series_on_ball_change_origin k radius_pos).has_sum x_mem_ball,
      rw zero_add at this,
      refine has_sum.sigma_of_has_sum this (λ l, _) _,
      { simp only [change_origin_series, continuous_multilinear_map.sum_apply],
        apply has_sum_fintype },
      { refine summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₂
          (mem_emetric_ball_zero_iff.1 x_mem_ball) k) (λ s, _),
        refine (continuous_multilinear_map.le_op_nnnorm _ _).trans_eq _,
        simp } } },
  refine hf.unique (change_origin_index_equiv.symm.has_sum_iff.1 _),
  refine has_sum.sigma_of_has_sum (p.has_sum x_add_y_mem_ball) (λ n, _)
    (change_origin_index_equiv.symm.summable_iff.2 hsf),
  erw [(p n).map_add_univ (λ _, x) (λ _, y)],
  convert has_sum_fintype _,
  ext1 s,
  dsimp only [f, change_origin_series_term, (∘), change_origin_index_equiv_symm_apply_fst,
    change_origin_index_equiv_symm_apply_snd_fst, change_origin_index_equiv_symm_apply_snd_snd_coe],
  rw continuous_multilinear_map.curry_fin_finset_apply_const,
  have : ∀ m (hm : n = m), p n (s.piecewise (λ _, x) (λ _, y)) =
    p m ((s.map (fin.cast hm).to_equiv.to_embedding).piecewise (λ _, x) (λ _, y)),
  { rintro m rfl, simp },
  apply this
end

end formal_multilinear_series

section

variables [complete_space F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x y : E}
{r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem has_fpower_series_on_ball.change_origin
  (hf : has_fpower_series_on_ball f p x r) (h : (‖y‖₊ : ℝ≥0∞) < r) :
  has_fpower_series_on_ball f (p.change_origin y) (x + y) (r - ‖y‖₊) :=
{ r_le := begin
    apply le_trans _ p.change_origin_radius,
    exact tsub_le_tsub hf.r_le le_rfl
  end,
  r_pos := by simp [h],
  has_sum := λ z hz, begin
    convert (p.change_origin y).has_sum _,
    { rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_comm] at hz,
      rw [p.change_origin_eval (hz.trans_le hf.r_le), add_assoc, hf.sum],
      refine mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt _ hz),
      exact_mod_cast nnnorm_add_le y z },
    { refine emetric.ball_subset_ball (le_trans _ p.change_origin_radius) hz,
      exact tsub_le_tsub hf.r_le le_rfl }
  end }

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
lemma has_fpower_series_on_ball.analytic_at_of_mem
  (hf : has_fpower_series_on_ball f p x r) (h : y ∈ emetric.ball x r) :
  analytic_at 𝕜 f y :=
begin
  have : (‖y - x‖₊ : ℝ≥0∞) < r, by simpa [edist_eq_coe_nnnorm_sub] using h,
  have := hf.change_origin this,
  rw [add_sub_cancel'_right] at this,
  exact this.analytic_at
end

lemma has_fpower_series_on_ball.analytic_on (hf : has_fpower_series_on_ball f p x r) :
  analytic_on 𝕜 f (emetric.ball x r) :=
λ y hy, hf.analytic_at_of_mem hy

variables (𝕜 f)

/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
lemma is_open_analytic_at : is_open {x | analytic_at 𝕜 f x} :=
begin
  rw is_open_iff_mem_nhds,
  rintro x ⟨p, r, hr⟩,
  exact mem_of_superset (emetric.ball_mem_nhds _ hr.r_pos) (λ y hy, hr.analytic_at_of_mem hy)
end

end

section

open formal_multilinear_series

variables {p : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E} {z₀ : 𝕜}

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`has_fpower_series_at` depends on `p.radius`. -/
lemma has_fpower_series_at_iff : has_fpower_series_at f p z₀ ↔
  ∀ᶠ z in 𝓝 0, has_sum (λ n, z ^ n • p.coeff n) (f (z₀ + z)) :=
begin
  refine ⟨λ ⟨r, r_le, r_pos, h⟩, eventually_of_mem (emetric.ball_mem_nhds 0 r_pos)
    (λ _, by simpa using h), _⟩,
  simp only [metric.eventually_nhds_iff],
  rintro ⟨r, r_pos, h⟩,
  refine ⟨p.radius ⊓ r.to_nnreal, by simp, _, _⟩,
  { simp only [r_pos.lt, lt_inf_iff, ennreal.coe_pos, real.to_nnreal_pos, and_true],
    obtain ⟨z, z_pos, le_z⟩ := normed_field.exists_norm_lt 𝕜 r_pos.lt,
    have : (‖z‖₊ : ennreal) ≤ p.radius,
    by { simp only [dist_zero_right] at h,
      apply formal_multilinear_series.le_radius_of_tendsto,
      convert tendsto_norm.comp (h le_z).summable.tendsto_at_top_zero,
      funext; simp [norm_smul, mul_comm] },
    refine lt_of_lt_of_le _ this,
    simp only [ennreal.coe_pos],
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos)) },
  { simp only [emetric.mem_ball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coeff, and_imp,
      dist_zero_right] at h ⊢,
    refine λ y hyp hyr, h _,
    simpa [nndist_eq_nnnorm, real.lt_to_nnreal_iff_coe_lt] using hyr }
end

lemma has_fpower_series_at_iff' : has_fpower_series_at f p z₀ ↔
  ∀ᶠ z in 𝓝 z₀, has_sum (λ n, (z - z₀) ^ n • p.coeff n) (f z) :=
begin
  rw [← map_add_left_nhds_zero, eventually_map, has_fpower_series_at_iff],
  congrm ∀ᶠ z in (𝓝 0 : filter 𝕜), has_sum (λ n, _) (f (z₀ + z)),
  rw add_sub_cancel'
end

end
