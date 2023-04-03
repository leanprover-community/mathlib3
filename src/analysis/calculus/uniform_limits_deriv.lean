/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import analysis.calculus.mean_value
import analysis.normed_space.is_R_or_C
import order.filter.curry

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_locally_uniformly_at`.

## Main statements

* `uniform_cauchy_seq_on_filter_of_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → E → (E →L[𝕜] G)` on a neighborhood of `x`,
    2. the functions `f` converge at `x`, and
    3. the derivatives `f'` form a Cauchy sequence uniformly on a neighborhood of `x`,
  then the `f` form a Cauchy sequence _uniformly_ on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on_filter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `f'` is the derivative of
  `g` on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on`: An often-easier-to-use version of the above theorem when
  *all* the derivatives exist and functions converge on a common open set and the derivatives
  converge uniformly there.

Each of the above statements also has variations that support `deriv` instead of `fderiv`.

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of the `g` converge to the `g'`.
That is, we want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in at_top, tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top ×ᶠ 𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifer order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top.curry (𝓝 x)) (𝓝 0)
```

Then the above implications are `filter.tendsto.curry` and
`filter.tendsto.mono_left filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `has_fderiv_at_of_tendsto_uniformly_on_filter` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried filters.

## Tags

uniform convergence, limits of derivatives
-/

open filter
open_locale uniformity filter topology

section limits_of_derivatives

variables {ι : Type*} {l : filter ι}
  {E : Type*} [normed_add_comm_group E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : ι → E → G} {g : E → G} {f' : ι → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {x : E}

/-- If a sequence of functions real or complex functions are eventually differentiable on a
neighborhood of `x`, they are Cauchy _at_ `x`, and their derivatives
are a uniform Cauchy sequence in a neighborhood of `x`, then the functions form a uniform Cauchy
sequence in a neighborhood of `x`. -/
lemma uniform_cauchy_seq_on_filter_of_fderiv
  (hf' : uniform_cauchy_seq_on_filter f' l (𝓝 x))
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.1) (f' n.1 n.2) n.2)
  (hfg : cauchy (map (λ n, f n x) l)) :
  uniform_cauchy_seq_on_filter f l (𝓝 x) :=
begin
  letI : normed_space ℝ E, from normed_space.restrict_scalars ℝ 𝕜 _,
  rw seminormed_add_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero at
    hf' ⊢,

  suffices : tendsto_uniformly_on_filter
    (λ (n : ι × ι) (z : E), f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0 (l ×ᶠ l) (𝓝 x) ∧
    tendsto_uniformly_on_filter (λ (n : ι × ι) (z : E), f n.1 x - f n.2 x) 0 (l ×ᶠ l) (𝓝 x),
  { have := this.1.add this.2,
    rw add_zero at this,
    exact this.congr (by simp), },
  split,
  { -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw metric.tendsto_uniformly_on_filter_iff at hf' ⊢,
    intros ε hε,
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right,
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this),
    obtain ⟨R, hR, hR'⟩ := metric.nhds_basis_ball.eventually_iff.mp d,
    let r := min 1 R,
    have hr : 0 < r, { simp [hR], },
    have hr' : ∀ ⦃y : E⦄, y ∈ metric.ball x r → c y,
    { exact (λ y hy, hR' (lt_of_lt_of_le (metric.mem_ball.mp hy) (min_le_right _ _))), },
    have hxy : ∀ (y : E), y ∈ metric.ball x r → ‖y - x‖ < 1,
    { intros y hy,
      rw [metric.mem_ball, dist_eq_norm] at hy,
      exact lt_of_lt_of_le hy (min_le_left _ _), },
    have hxyε : ∀ (y : E), y ∈ metric.ball x r → ε * ‖y - x‖ < ε,
    { intros y hy,
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy), },

    -- With a small ball in hand, apply the mean value theorem
    refine eventually_prod_iff.mpr ⟨_, b, (λ e : E, metric.ball x r e),
      eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr), (λ n hn y hy, _)⟩,
    simp only [pi.zero_apply, dist_zero_left] at e ⊢,
    refine lt_of_le_of_lt _ (hxyε y hy),
    exact convex.norm_image_sub_le_of_norm_has_fderiv_within_le
      (λ y hy, ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).has_fderiv_within_at)
      (λ y hy, (e hn (hr' hy)).1.le)
      (convex_ball x r) (metric.mem_ball_self hr) hy, },
  { -- This is just `hfg` run through `eventually_prod_iff`
    refine metric.tendsto_uniformly_on_filter_iff.mpr (λ ε hε, _),
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg).2 ε hε,
    exact eventually_prod_iff.mpr
    ⟨ (λ (n : ι × ι), (f n.1 x ∈ t) ∧ (f n.2 x ∈ t)),
      eventually_prod_iff.mpr ⟨_, ht, _, ht, (λ n hn n' hn', ⟨hn, hn'⟩)⟩,
      (λ y, true),
      (by simp),
      (λ n hn y hy, by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2)⟩, },
end

/-- A variant of the second fundamental theorem of calculus (FTC-2): If a sequence of functions
between real or complex normed spaces are differentiable on a ball centered at `x`, they
form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy uniformly on the ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work with power series
and Dirichlet series (our primary use case). However, this can be generalized by replacing the ball
with any connected, bounded, open set and replacing uniform convergence with local uniform
convergence. See `cauchy_map_of_uniform_cauchy_seq_on_fderiv`.
-/
lemma uniform_cauchy_seq_on_ball_of_fderiv
  {r : ℝ} (hf' : uniform_cauchy_seq_on f' l (metric.ball x r))
  (hf : ∀ n : ι, ∀ y : E, y ∈ metric.ball x r → has_fderiv_at (f n) (f' n y) y)
  (hfg : cauchy (map (λ n, f n x) l)) :
  uniform_cauchy_seq_on f l (metric.ball x r) :=
begin
  letI : normed_space ℝ E, from normed_space.restrict_scalars ℝ 𝕜 _,
  haveI : ne_bot l, from (cauchy_map_iff.1 hfg).1,
  rcases le_or_lt r 0 with hr|hr,
  { simp only [metric.ball_eq_empty.2 hr, uniform_cauchy_seq_on, set.mem_empty_iff_false,
      is_empty.forall_iff, eventually_const, implies_true_iff] },
  rw seminormed_add_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero at hf' ⊢,
  suffices : tendsto_uniformly_on
    (λ (n : ι × ι) (z : E), f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
      (l ×ᶠ l) (metric.ball x r) ∧
    tendsto_uniformly_on (λ (n : ι × ι) (z : E), f n.1 x - f n.2 x) 0
      (l ×ᶠ l) (metric.ball x r),
  { have := this.1.add this.2,
    rw add_zero at this,
    refine this.congr _,
    apply eventually_of_forall,
    intros n z hz,
    simp, },
  split,
  { -- This inequality follows from the mean value theorem
    rw metric.tendsto_uniformly_on_iff at hf' ⊢,
    intros ε hε,
    obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ q * r < ε,
    { simp_rw mul_comm,
      exact exists_pos_mul_lt hε.lt r, },
    apply (hf' q hqpos.gt).mono,
    intros n hn y hy,
    simp_rw [dist_eq_norm, pi.zero_apply, zero_sub, norm_neg] at hn ⊢,
    have mvt := convex.norm_image_sub_le_of_norm_has_fderiv_within_le
      (λ z hz, ((hf n.1 z hz).sub (hf n.2 z hz)).has_fderiv_within_at)
      (λ z hz, (hn z hz).le) (convex_ball x r) (metric.mem_ball_self hr) hy,
    refine lt_of_le_of_lt mvt _,
    have : q * ‖y - x‖ < q * r,
    { exact mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using metric.mem_ball.mp hy)
        (norm_nonneg _) hqpos, },
    exact this.trans hq, },
  { -- This is just `hfg` run through `eventually_prod_iff`
    refine metric.tendsto_uniformly_on_iff.mpr (λ ε hε, _),
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg).2 ε hε,
    rw eventually_prod_iff,
    refine ⟨(λ n, f n x ∈ t), ht, (λ n, f n x ∈ t), ht, _⟩,
    intros n hn n' hn' z hz,
    rw [dist_eq_norm, pi.zero_apply, zero_sub, norm_neg, ←dist_eq_norm],
    exact (ht' _ hn _ hn'), },
end

/-- If a sequence of functions between real or complex normed spaces are differentiable on a
preconnected open set, they form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy
uniformly on the set, then the functions form a Cauchy sequence at any point in the set. -/
lemma cauchy_map_of_uniform_cauchy_seq_on_fderiv
  {s : set E} (hs : is_open s) (h's : is_preconnected s)
  (hf' : uniform_cauchy_seq_on f' l s)
  (hf : ∀ n : ι, ∀ y : E, y ∈ s → has_fderiv_at (f n) (f' n y) y)
  {x₀ x : E} (hx₀ : x₀ ∈ s) (hx : x ∈ s)
  (hfg : cauchy (map (λ n, f n x₀) l)) :
  cauchy (map (λ n, f n x) l) :=
begin
  haveI : ne_bot l, from (cauchy_map_iff.1 hfg).1,
  let t := {y | y ∈ s ∧ cauchy (map (λ n, f n y) l)},
  suffices H : s ⊆ t, from (H hx).2,
  have A : ∀ x ε, x ∈ t → metric.ball x ε ⊆ s → metric.ball x ε ⊆ t,
  from λ x ε xt hx y hy, ⟨hx hy, (uniform_cauchy_seq_on_ball_of_fderiv (hf'.mono hx)
    (λ n y hy, hf n y (hx hy)) xt.2).cauchy_map hy⟩,
  have open_t : is_open t,
  { rw metric.is_open_iff,
    assume x hx,
    rcases metric.is_open_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩,
    exact ⟨ε, εpos, A x ε hx hε⟩ },
  have st_nonempty : (s ∩ t).nonempty, from ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩,
  suffices H : closure t ∩ s ⊆ t, from h's.subset_of_closure_inter_subset open_t st_nonempty H,
  rintros x ⟨xt, xs⟩,
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), metric.ball x ε ⊆ s,
    from metric.is_open_iff.1 hs x xs,
  obtain ⟨y, yt, hxy⟩ : ∃ (y : E) (yt : y ∈ t), dist x y < ε / 2,
    from metric.mem_closure_iff.1 xt _ (half_pos εpos),
  have B : metric.ball y (ε / 2) ⊆ metric.ball x ε,
  { apply metric.ball_subset_ball', rw dist_comm, linarith },
  exact A y (ε / 2) yt (B.trans hε) (metric.mem_ball.2 hxy)
end

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `‖z - y‖⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `‖z - y‖⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  (hf' : tendsto_uniformly_on_filter f' g' l (𝓝 x))
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.1) (f' n.1 n.2) n.2)
  (hfg : ∀ᶠ (y : E) in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y))) :
  tendsto_uniformly_on_filter
    (λ n : ι, λ y : E, (‖y - x‖⁻¹ : 𝕜) • (f n y - f n x))
    (λ y : E, (‖y - x‖⁻¹ : 𝕜) • (g y - g x))
    l (𝓝 x) :=
begin
  letI : normed_space ℝ E, from normed_space.restrict_scalars ℝ 𝕜 _,
  rcases eq_or_ne l ⊥ with hl|hl,
  { simp only [hl, tendsto_uniformly_on_filter, bot_prod, eventually_bot, implies_true_iff] },
  haveI : ne_bot l := ⟨hl⟩,
  refine uniform_cauchy_seq_on_filter.tendsto_uniformly_on_filter_of_tendsto _
    ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono (λ y hy, (hy.1.sub hy.2).const_smul _)),
  rw seminormed_add_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero,
  rw metric.tendsto_uniformly_on_filter_iff,

  have hfg' := hf'.uniform_cauchy_seq_on_filter,
  rw seminormed_add_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero at hfg',
  rw metric.tendsto_uniformly_on_filter_iff at hfg',
  intros ε hε,
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε,
  specialize hfg' (q : ℝ) (by simp [hqpos]),

  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right,
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this),
  obtain ⟨r, hr, hr'⟩ := metric.nhds_basis_ball.eventually_iff.mp d,

  rw eventually_prod_iff,
  refine ⟨_, b, (λ e : E, metric.ball x r e),
    eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr), (λ n hn y hy, _)⟩,
  simp only [pi.zero_apply, dist_zero_left],
  rw [← smul_sub, norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  refine lt_of_le_of_lt _ hqε,
  by_cases hyz' : x = y, { simp [hyz', hqpos.le], },
  have hyz : 0 < ‖y - x‖,
  {rw norm_pos_iff, intros hy', exact hyz' (eq_of_sub_eq_zero hy').symm, },
  rw [inv_mul_le_iff hyz, mul_comm, sub_sub_sub_comm],
  simp only [pi.zero_apply, dist_zero_left] at e,
  refine convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    (λ y hy, ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).has_fderiv_within_at)
    (λ y hy, (e hn (hr' hy)).1.le)
    (convex_ball x r) (metric.mem_ball_self hr) hy,
end

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficiently large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x` -/
lemma has_fderiv_at_of_tendsto_uniformly_on_filter [ne_bot l]
  (hf' : tendsto_uniformly_on_filter f' g' l (𝓝 x))
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.1) (f' n.1 n.2) n.2)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y))) :
  has_fderiv_at g (g' x) x :=
begin
  -- The proof strategy follows several steps:
  --   1. The quantifiers in the definition of the derivative are
  --      `∀ ε > 0, ∃δ > 0, ∀y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  --      `∀ ε > 0, ∃N, ∀n ≥ N, ∃δ > 0, ∀y ∈ B_δ(x)` which will allow us to introduce the `f(') n`
  --   2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  --      the quantifiers using the uniform convergence assumption
  rw has_fderiv_at_iff_tendsto,

  -- Introduce extra quantifier via curried filters
  suffices : tendsto
    (λ (y : ι × E), ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖) (l.curry (𝓝 x)) (𝓝 0),
  { rw metric.tendsto_nhds at this ⊢,
    intros ε hε,
    specialize this ε hε,
    rw eventually_curry_iff at this,
    simp only at this,
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const]), },

  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  --   * The difference functions of the `f n` converge *uniformly* to the difference functions
  --     of the `g n`
  --   * The `f' n` are the derivatives of the `f n`
  --   * The `f' n` converge to `g'` at `x`
  conv
  { congr, funext,
    rw [←norm_norm, ←norm_inv,←@is_R_or_C.norm_of_real 𝕜 _ _,
      is_R_or_C.of_real_inv, ←norm_smul], },
  rw ←tendsto_zero_iff_norm_tendsto_zero,
  have : (λ a : ι × E, (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
    (λ a : ι × E, (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
    (λ a : ι × E, (‖a.2 - x‖⁻¹ : 𝕜) • ((f a.1 a.2 - f a.1 x) -
      ((f' a.1 x) a.2 - (f' a.1 x) x))) +
    (λ a : ι × E, (‖a.2 - x‖⁻¹ : 𝕜) • ((f' a.1 x - g' x) (a.2 - x))),
  { ext, simp only [pi.add_apply], rw [←smul_add, ←smul_add], congr,
  simp only [map_sub, sub_add_sub_cancel, continuous_linear_map.coe_sub', pi.sub_apply], },
  simp_rw this,
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0), simp only [add_zero],
  rw this,
  refine tendsto.add (tendsto.add _ _) _,
  simp only,
  { have := difference_quotients_converge_uniformly hf' hf hfg,
    rw metric.tendsto_uniformly_on_filter_iff at this,
    rw metric.tendsto_nhds,
    intros ε hε,
    apply ((this ε hε).filter_mono curry_le_prod).mono,
    intros n hn,
    rw dist_eq_norm at hn ⊢,
    rw ← smul_sub at hn,
    rwa sub_zero, },
  { -- (Almost) the definition of the derivatives
    rw metric.tendsto_nhds,
    intros ε hε,
    rw eventually_curry_iff,
    refine hf.curry.mono (λ n hn, _),
    have := hn.self_of_nhds,
    rw [has_fderiv_at_iff_tendsto, metric.tendsto_nhds] at this,
    refine (this ε hε).mono (λ y hy, _),
    rw dist_eq_norm at hy ⊢,
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢,
    rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    exact hy, },
  { -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine tendsto.mono_left _ curry_le_prod,
    have h1: tendsto (λ n : ι × E, g' n.2 - f' n.1 n.2) (l ×ᶠ 𝓝 x) (𝓝 0),
    { rw metric.tendsto_uniformly_on_filter_iff at hf',
      exact metric.tendsto_nhds.mpr (λ ε hε, by simpa using hf' ε hε), },
    have h2: tendsto (λ n : ι, g' x - f' n x) l (𝓝 0),
    { rw metric.tendsto_nhds at h1 ⊢,
      exact (λ ε hε, (h1 ε hε).curry.mono (λ n hn, hn.self_of_nhds)), },
    have := (tendsto_fst.comp (h2.prod_map tendsto_id)),
    refine squeeze_zero_norm _ (tendsto_zero_iff_norm_tendsto_zero.mp this),
    intros n,
    simp_rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    by_cases hx : x = n.2, { simp [hx], },
    have hnx : 0 < ‖n.2 - x‖,
    { rw norm_pos_iff, intros hx', exact hx (eq_of_sub_eq_zero hx').symm, },
    rw [inv_mul_le_iff hnx, mul_comm],
    simp only [function.comp_app, prod_map],
    rw norm_sub_rev,
    exact (f' n.1 x - g' x).le_op_norm (n.2 - x), },
end

lemma has_fderiv_at_of_tendsto_locally_uniformly_on [ne_bot l] {s : set E} (hs : is_open s)
  (hf' : tendsto_locally_uniformly_on f' g' l s)
  (hf : ∀ n, ∀ x ∈ s, has_fderiv_at (f n) (f' n x) x)
  (hfg : ∀ x ∈ s, tendsto (λ n, f n x) l (𝓝 (g x)))
  (hx : x ∈ s) :
  has_fderiv_at g (g' x) x :=
begin
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx,
  have h3 : set.univ ×ˢ s ∈ l ×ᶠ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self],
  have h4 : ∀ᶠ (n : ι × E) in l ×ᶠ 𝓝 x, has_fderiv_at (f n.1) (f' n.1 n.2) n.2,
    from eventually_of_mem h3 (λ ⟨n, z⟩ ⟨hn, hz⟩, hf n z hz),
  refine has_fderiv_at_of_tendsto_uniformly_on_filter _ h4 (eventually_of_mem h1 hfg),
  simpa [is_open.nhds_within_eq hs hx] using tendsto_locally_uniformly_on_iff_filter.mp hf' x hx,
end

/-- A slight variant of `has_fderiv_at_of_tendsto_locally_uniformly_on` with the assumption stated
in terms of `differentiable_on` rather than `has_fderiv_at`. This makes a few proofs nicer in
complex analysis where holomorphicity is assumed but the derivative is not known a priori. -/
lemma has_fderiv_at_of_tendsto_locally_uniformly_on' [ne_bot l] {s : set E} (hs : is_open s)
  (hf' : tendsto_locally_uniformly_on (fderiv 𝕜 ∘ f) g' l s)
  (hf : ∀ n, differentiable_on 𝕜 (f n) s)
  (hfg : ∀ x ∈ s, tendsto (λ n, f n x) l (𝓝 (g x)))
  (hx : x ∈ s) :
  has_fderiv_at g (g' x) x :=
begin
  refine has_fderiv_at_of_tendsto_locally_uniformly_on hs hf' (λ n z hz, _) hfg hx,
  exact ((hf n z hz).differentiable_at (hs.mem_nhds hz)).has_fderiv_at
end

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`. -/
lemma has_fderiv_at_of_tendsto_uniformly_on [ne_bot l]
  {s : set E} (hs : is_open s)
  (hf' : tendsto_uniformly_on f' g' l s)
  (hf : ∀ (n : ι), ∀ (x : E), x ∈ s → has_fderiv_at (f n) (f' n x) x)
  (hfg : ∀ (x : E), x ∈ s → tendsto (λ n, f n x) l (𝓝 (g x))) :
  ∀ (x : E), x ∈ s → has_fderiv_at g (g' x) x :=
λ x, has_fderiv_at_of_tendsto_locally_uniformly_on hs hf'.tendsto_locally_uniformly_on hf hfg

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit. -/
lemma has_fderiv_at_of_tendsto_uniformly [ne_bot l]
  (hf' : tendsto_uniformly f' g' l)
  (hf : ∀ (n : ι), ∀ (x : E), has_fderiv_at (f n) (f' n x) x)
  (hfg : ∀ (x : E), tendsto (λ n, f n x) l (𝓝 (g x))) :
  ∀ (x : E), has_fderiv_at g (g' x) x :=
begin
  intros x,
  have hf : ∀ (n : ι), ∀ (x : E), x ∈ set.univ → has_fderiv_at (f n) (f' n x) x, { simp [hf], },
  have hfg : ∀ (x : E), x ∈ set.univ → tendsto (λ n, f n x) l (𝓝 (g x)), { simp [hfg], },
  have hf' : tendsto_uniformly_on f' g' l set.univ, { rwa tendsto_uniformly_on_univ, },
  refine has_fderiv_at_of_tendsto_uniformly_on is_open_univ hf' hf hfg x (set.mem_univ x),
end

end limits_of_derivatives

section deriv

/-! ### `deriv` versions of above theorems

In this section, we provide `deriv` equivalents of the `fderiv` lemmas in the previous section.
The protected function `promote_deriv` provides the translation between derivatives and Fréchet
derivatives
-/

variables {ι : Type*} {l : filter ι}
  {𝕜 : Type*} [is_R_or_C 𝕜]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : ι → 𝕜 → G} {g : 𝕜 → G} {f' : ι → 𝕜 → G} {g' : 𝕜 → G}
  {x : 𝕜}

/-- If our derivatives converge uniformly, then the Fréchet derivatives converge uniformly -/
lemma uniform_cauchy_seq_on_filter.one_smul_right {l' : filter 𝕜}
  (hf' : uniform_cauchy_seq_on_filter f' l l') :
  uniform_cauchy_seq_on_filter (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)) l l' :=
begin
  -- The tricky part of this proof is that operator norms are written in terms of `≤` whereas
  -- metrics are written in terms of `<`. So we need to shrink `ε` utilizing the archimedean
  -- property of `ℝ`

  rw [seminormed_add_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero,
      metric.tendsto_uniformly_on_filter_iff] at hf' ⊢,
  intros ε hε,
  obtain ⟨q, hq, hq'⟩ := exists_between hε.lt,
  apply (hf' q hq).mono,
  intros n hn,
  refine lt_of_le_of_lt _ hq',
  simp only [dist_eq_norm, pi.zero_apply, zero_sub, norm_neg] at hn ⊢,
  refine continuous_linear_map.op_norm_le_bound _ hq.le _,
  intros z,
  simp only [continuous_linear_map.coe_sub', pi.sub_apply, continuous_linear_map.smul_right_apply,
    continuous_linear_map.one_apply],
  rw [←smul_sub, norm_smul, mul_comm],
  exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le,
end

lemma uniform_cauchy_seq_on_filter_of_deriv
  (hf' : uniform_cauchy_seq_on_filter f' l (𝓝 x))
  (hf : ∀ᶠ (n : ι × 𝕜) in (l ×ᶠ 𝓝 x), has_deriv_at (f n.1) (f' n.1 n.2) n.2)
  (hfg : cauchy (map (λ n, f n x) l)) :
  uniform_cauchy_seq_on_filter f l (𝓝 x) :=
begin
  simp_rw has_deriv_at_iff_has_fderiv_at at hf,
  exact uniform_cauchy_seq_on_filter_of_fderiv
    hf'.one_smul_right hf hfg,
end

lemma uniform_cauchy_seq_on_ball_of_deriv
  {r : ℝ} (hf' : uniform_cauchy_seq_on f' l (metric.ball x r))
  (hf : ∀ n : ι, ∀ y : 𝕜, y ∈ metric.ball x r → has_deriv_at (f n) (f' n y) y)
  (hfg : cauchy (map (λ n, f n x) l)) :
  uniform_cauchy_seq_on f l (metric.ball x r) :=
begin
  simp_rw has_deriv_at_iff_has_fderiv_at at hf,
  rw uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter at hf',
  have hf' : uniform_cauchy_seq_on (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)) l
    (metric.ball x r),
  { rw uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter,
    exact hf'.one_smul_right, },
  exact uniform_cauchy_seq_on_ball_of_fderiv hf' hf hfg,
end

lemma has_deriv_at_of_tendsto_uniformly_on_filter [ne_bot l]
  (hf' : tendsto_uniformly_on_filter f' g' l (𝓝 x))
  (hf : ∀ᶠ (n : ι × 𝕜) in (l ×ᶠ 𝓝 x), has_deriv_at (f n.1) (f' n.1 n.2) n.2)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y))) :
  has_deriv_at g (g' x) x :=
begin
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `has_fderiv_at_of_tendsto_uniformly_on_filter`
  let F' := (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)),
  let G' := λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (g' z),
  simp_rw has_deriv_at_iff_has_fderiv_at at hf ⊢,

  -- Now we need to rewrite hf' in terms of continuous_linear_maps. The tricky part is that
  -- operator norms are written in terms of `≤` whereas metrics are written in terms of `<`. So we
  -- need to shrink `ε` utilizing the archimedean property of `ℝ`
  have hf' : tendsto_uniformly_on_filter F' G' l (𝓝 x),
  { rw metric.tendsto_uniformly_on_filter_iff at hf' ⊢,
    intros ε hε,
    obtain ⟨q, hq, hq'⟩ := exists_between hε.lt,
    apply (hf' q hq).mono,
    intros n hn,
    refine lt_of_le_of_lt _ hq',
    simp only [F', G', dist_eq_norm] at hn ⊢,
    refine continuous_linear_map.op_norm_le_bound _ hq.le _,
    intros z,
    simp only [continuous_linear_map.coe_sub', pi.sub_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply],
    rw [←smul_sub, norm_smul, mul_comm],
    exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le, },
  exact has_fderiv_at_of_tendsto_uniformly_on_filter hf' hf hfg,
end

lemma has_deriv_at_of_tendsto_locally_uniformly_on [ne_bot l] {s : set 𝕜} (hs : is_open s)
  (hf' : tendsto_locally_uniformly_on f' g' l s)
  (hf : ∀ᶠ n in l, ∀ x ∈ s, has_deriv_at (f n) (f' n x) x)
  (hfg : ∀ x ∈ s, tendsto (λ n, f n x) l (𝓝 (g x)))
  (hx : x ∈ s) :
  has_deriv_at g (g' x) x :=
begin
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx,
  have h2 : ∀ᶠ (n : ι × 𝕜) in l ×ᶠ 𝓝 x, has_deriv_at (f n.1) (f' n.1 n.2) n.2,
    from eventually_prod_iff.2 ⟨_, hf, λ x, x ∈ s, h1, λ n, id⟩,
  refine has_deriv_at_of_tendsto_uniformly_on_filter _ h2 (eventually_of_mem h1 hfg),
  simpa [is_open.nhds_within_eq hs hx] using tendsto_locally_uniformly_on_iff_filter.mp hf' x hx,
end

/-- A slight variant of `has_deriv_at_of_tendsto_locally_uniformly_on` with the assumption stated in
terms of `differentiable_on` rather than `has_deriv_at`. This makes a few proofs nicer in complex
analysis where holomorphicity is assumed but the derivative is not known a priori. -/
lemma has_deriv_at_of_tendsto_locally_uniformly_on' [ne_bot l] {s : set 𝕜} (hs : is_open s)
  (hf' : tendsto_locally_uniformly_on (deriv ∘ f) g' l s)
  (hf : ∀ᶠ n in l, differentiable_on 𝕜 (f n) s)
  (hfg : ∀ x ∈ s, tendsto (λ n, f n x) l (𝓝 (g x)))
  (hx : x ∈ s) :
  has_deriv_at g (g' x) x :=
begin
  refine has_deriv_at_of_tendsto_locally_uniformly_on hs hf' _ hfg hx,
  filter_upwards [hf] with n h z hz using ((h z hz).differentiable_at (hs.mem_nhds hz)).has_deriv_at
end

lemma has_deriv_at_of_tendsto_uniformly_on [ne_bot l]
  {s : set 𝕜} (hs : is_open s)
  (hf' : tendsto_uniformly_on f' g' l s)
  (hf : ∀ᶠ n in l, ∀ (x : 𝕜), x ∈ s → has_deriv_at (f n) (f' n x) x)
  (hfg : ∀ (x : 𝕜), x ∈ s → tendsto (λ n, f n x) l (𝓝 (g x))) :
  ∀ (x : 𝕜), x ∈ s → has_deriv_at g (g' x) x :=
λ x, has_deriv_at_of_tendsto_locally_uniformly_on hs hf'.tendsto_locally_uniformly_on hf hfg

lemma has_deriv_at_of_tendsto_uniformly [ne_bot l]
  (hf' : tendsto_uniformly f' g' l)
  (hf : ∀ᶠ n in l, ∀ (x : 𝕜), has_deriv_at (f n) (f' n x) x)
  (hfg : ∀ (x : 𝕜), tendsto (λ n, f n x) l (𝓝 (g x))) :
  ∀ (x : 𝕜), has_deriv_at g (g' x) x :=
begin
  intros x,
  have hf : ∀ᶠ n in l, ∀ (x : 𝕜), x ∈ set.univ → has_deriv_at (f n) (f' n x) x,
    by filter_upwards [hf] with n h x hx using h x,
  have hfg : ∀ (x : 𝕜), x ∈ set.univ → tendsto (λ n, f n x) l (𝓝 (g x)), { simp [hfg], },
  have hf' : tendsto_uniformly_on f' g' l set.univ, { rwa tendsto_uniformly_on_univ, },
  exact has_deriv_at_of_tendsto_uniformly_on is_open_univ hf' hf hfg x (set.mem_univ x),
end

end deriv
