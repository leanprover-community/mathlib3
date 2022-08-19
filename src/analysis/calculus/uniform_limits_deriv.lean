/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import analysis.calculus.mean_value
import analysis.normed_space.is_R_or_C

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_locally_uniformly_at`.

## Main statements

* `uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → (E → (E →L[𝕜] G))` on a neighborhood of `x`,
    2.the `f` converge at `x`, and
    3. the `f'` converge uniformly on a neighborhood of `x`,
  then the `f` converge _uniformly_ on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on_filter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `g'` is the derivative of
  `g` on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on`: An often-easier-to-use version of the above theorem when
  all *all* the derivatives exist and functions converge on a common open set and the derivatives
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
continuous, then you can avoid the mean value theorem and much of the work around curried fitlers.

## Tags

uniform convergence, limits of derivatives
-/

section filter_curry

variables {α β γ : Type*}

/-- This filter is characterized by `filter.eventually_curry_iff`:
`(∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y)`. Useful
in adding quantifiers to the middle of `tendsto`s. See
`has_fderiv_at_of_tendsto_uniformly_on_filter`. -/
def filter.curry (f : filter α) (g : filter β) : filter (α × β) :=
{ sets := { s | ∀ᶠ (a : α) in f, ∀ᶠ (b : β) in g, (a, b) ∈ s },
  univ_sets := (by simp only [set.mem_set_of_eq, set.mem_univ, filter.eventually_true]),
  sets_of_superset := begin
    intros x y hx hxy,
    simp only [set.mem_set_of_eq] at hx ⊢,
    exact hx.mono (λ a ha, ha.mono(λ b hb, set.mem_of_subset_of_mem hxy hb)),
  end,
  inter_sets := begin
    intros x y hx hy,
    simp only [set.mem_set_of_eq, set.mem_inter_eq] at hx hy ⊢,
    exact (hx.and hy).mono (λ a ha, (ha.1.and ha.2).mono (λ b hb, hb)),
  end, }

lemma filter.eventually_curry_iff {f : filter α} {g : filter β} {p : α × β → Prop} :
  (∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y) :=
begin
  simp only [filter.curry],
  rw filter.eventually_iff,
  simp only [filter.mem_mk, set.mem_set_of_eq],
end

lemma filter.curry_le_prod {f : filter α} {g : filter β} :
  f.curry g ≤ f.prod g :=
begin
  intros u hu,
  rw ←filter.eventually_mem_set at hu ⊢,
  rw filter.eventually_curry_iff,
  exact hu.curry,
end

lemma filter.tendsto.curry {f : α → β → γ} {la : filter α} {lb : filter β} {lc : filter γ} :
  (∀ᶠ a in la, filter.tendsto (λ b : β, f a b) lb lc) → filter.tendsto ↿f (la.curry lb) lc :=
begin
  intros h,
  rw filter.tendsto_def,
  simp only [filter.curry, filter.mem_mk, set.mem_set_of_eq, set.mem_preimage],
  simp_rw filter.tendsto_def at h,
  refine (λ s hs, h.mono (λ a ha, filter.eventually_iff.mpr _)),
  simpa [function.has_uncurry.uncurry, set.preimage] using ha s hs,
end

end filter_curry

open filter
open_locale uniformity filter topological_space

section limits_of_derivatives

variables {ι : Type*} {l : filter ι} [ne_bot l]
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : ι → E → G} {g : E → G} {f' : ι → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {x : E}

/-- If a sequence of functions real or complex functions are eventually differentiable on a
neighborhood of `x`, they converge pointwise _at_ `x`, and their derivatives
converge uniformly in a neighborhood of `x`, then the functions form a uniform Cauchy sequence
in a neighborhood of `x`. -/
lemma uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : uniform_cauchy_seq_on_filter f' l (𝓝 x)) :
  uniform_cauchy_seq_on_filter f l (𝓝 x) :=
begin
  rw normed_add_comm_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero at hfg' ⊢,

  suffices : tendsto_uniformly_on_filter
    (λ (n : ι × ι) (z : E), f n.fst z - f n.snd z - (f n.fst x - f n.snd x)) 0 (l ×ᶠ l) (𝓝 x) ∧
    tendsto_uniformly_on_filter (λ (n : ι × ι) (z : E), f n.fst x - f n.snd x) 0 (l ×ᶠ l) (𝓝 x),
  { have := this.1.add this.2,
    rw add_zero at this,
    exact this.congr (by simp), },
  split,
  { -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw metric.tendsto_uniformly_on_filter_iff at hfg' ⊢,
    intros ε hε,
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right,
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hfg' ε hε).and this),
    obtain ⟨R, hR, hR'⟩ := metric.nhds_basis_ball.eventually_iff.mp d,
    let r := min 1 R,
    have hr : 0 < r, { simp [hR], },
    have hr' : ∀ ⦃y : E⦄, y ∈ metric.ball x r → c y,
    { exact (λ y hy, hR' (lt_of_lt_of_le (metric.mem_ball.mp hy) (min_le_right _ _))), },
    have hxy : ∀ (y : E), y ∈ metric.ball x r → ∥y - x∥ < 1,
    { intros y hy,
      rw [metric.mem_ball, dist_eq_norm] at hy,
      exact lt_of_lt_of_le hy (min_le_left _ _), },
    have hxyε : ∀ (y : E), y ∈ metric.ball x r → ε * ∥y - x∥ < ε,
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
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg.cauchy_map).2 ε hε,
    exact eventually_prod_iff.mpr
    ⟨ (λ (n : ι × ι), (f n.fst x ∈ t) ∧ (f n.snd x ∈ t)),
      eventually_prod_iff.mpr ⟨_, ht, _, ht, (λ n hn n' hn', ⟨hn, hn'⟩)⟩,
      (λ y, true),
      (by simp),
      (λ n hn y hy, by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2)⟩, },
end

/-- A variant of the second fundamental theorem of calculus (FTC-2): If a sequence of functions
real or complex functions are differentiable on a ball centered at `x`, they
converge pointwise _at_ `x`, and their derivatives converge uniformly on the ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work with power series
and Dirichlet series (our primary use case). However, this can be generalized by replacing the ball
with any connected, bounded, open set and replacing uniform convergence with local uniform
convergence.
-/
lemma uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_fderiv
  {r : ℝ} (hr : 0 < r)
  (hf : ∀ n : ι, ∀ y : E, y ∈ metric.ball x r → has_fderiv_at (f n) (f' n y) y)
  (hfg : tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : uniform_cauchy_seq_on f' l (metric.ball x r)) :
  uniform_cauchy_seq_on f l (metric.ball x r) :=
begin
  rw normed_add_comm_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero at hfg' ⊢,

  suffices : tendsto_uniformly_on
    (λ (n : ι × ι) (z : E), f n.fst z - f n.snd z - (f n.fst x - f n.snd x)) 0 (l ×ᶠ l) (metric.ball x r) ∧
    tendsto_uniformly_on (λ (n : ι × ι) (z : E), f n.fst x - f n.snd x) 0 (l ×ᶠ l) (metric.ball x r),
  { have := this.1.add this.2,
    rw add_zero at this,
    refine this.congr _,
    apply eventually_of_forall,
    intros n z hz,
    simp, },
  split,
  { -- This inequality follows from the mean value theorem
    rw metric.tendsto_uniformly_on_iff at hfg' ⊢,
    intros ε hε,
    obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ q * r < ε,
    { simp_rw mul_comm,
      exact exists_pos_mul_lt hε.lt r, },
    apply (hfg' q hqpos.gt).mono,
    intros n hn y hy,
    simp_rw [dist_eq_norm, pi.zero_apply, zero_sub, norm_neg] at hn ⊢,
    have mvt := convex.norm_image_sub_le_of_norm_has_fderiv_within_le
      (λ z hz, ((hf n.fst z hz).sub (hf n.snd z hz)).has_fderiv_within_at)
      (λ z hz, (hn z hz).le) (convex_ball x r) (metric.mem_ball_self hr) hy,
    refine lt_of_le_of_lt mvt _,
    have : q * ∥y - x∥ < q * r,
    { exact mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using metric.mem_ball.mp hy)
        (norm_nonneg _) hqpos, },
    exact this.trans hq, },
  { -- This is just `hfg` run through `eventually_prod_iff`
    refine metric.tendsto_uniformly_on_iff.mpr (λ ε hε, _),
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg.cauchy_map).2 ε hε,
    rw eventually_prod_iff,
    refine ⟨(λ n, f n x ∈ t), ht, (λ n, f n x ∈ t), ht, _⟩,
    intros n hn n' hn' z hz,
    rw [dist_eq_norm, pi.zero_apply, zero_sub, norm_neg, ←dist_eq_norm],
    exact (ht' _ hn _ hn'), },
end

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ (y : E) in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on_filter f' g' l (𝓝 x)) :
  tendsto_uniformly_on_filter
    (λ n : ι, λ y : E, (∥y - x∥⁻¹ : 𝕜) • (f n y - f n x))
    (λ y : E, (∥y - x∥⁻¹ : 𝕜) • (g y - g x))
    l (𝓝 x) :=
begin
  refine uniform_cauchy_seq_on_filter.tendsto_uniformly_on_filter_of_tendsto _
    ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono (λ y hy, (hy.1.sub hy.2).const_smul _)),
  rw normed_add_comm_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero,
  rw metric.tendsto_uniformly_on_filter_iff,

  have hfg'' := hfg'.uniform_cauchy_seq_on_filter,
  rw normed_add_comm_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero at hfg'',
  rw metric.tendsto_uniformly_on_filter_iff at hfg'',
  intros ε hε,
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε,
  specialize hfg'' (q : ℝ) (by simp [hqpos]),

  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right,
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg''.and this),
  obtain ⟨r, hr, hr'⟩ := metric.nhds_basis_ball.eventually_iff.mp d,

  rw eventually_prod_iff,
  refine ⟨_, b, (λ e : E, metric.ball x r e),
    eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr), (λ n hn y hy, _)⟩,
  simp only [pi.zero_apply, dist_zero_left],
  rw [← smul_sub, norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  refine lt_of_le_of_lt _ hqε,
  by_cases hyz' : x = y, { simp [hyz', hqpos.le], },
  have hyz : 0 < ∥y - x∥,
  {rw norm_pos_iff, intros hy', exact hyz' (eq_of_sub_eq_zero hy').symm, },
  rw [inv_mul_le_iff hyz, mul_comm],
  have : ∀ a b c d : G, a - b - (c - d) = a - c - (b - d),
  { intros a b c d,
    rw [←sub_add, ←sub_add, sub_sub, sub_sub],
    conv { congr, congr, congr, skip, rw add_comm, }, },
  rw this,
  simp only [pi.zero_apply, dist_zero_left] at e,
  refine convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    (λ y hy, ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).has_fderiv_within_at)
    (λ y hy, (e hn (hr' hy)).1.le)
    (convex_ball x r) (metric.mem_ball_self hr) hy,
end

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf`: There is a neighborhood of `x` such that for all sufficiently large `n`, `f' n` is the
    derivative of `f n` **and** for all sufficiently large `N`, there is a neighborhood of `x`
    such that for all `n ≥ N`, `f' n` is the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x`
  * `hfg'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`! --/
lemma has_fderiv_at_of_tendsto_uniformly_on_filter
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on_filter f' g' l (𝓝 x)) :
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
    (λ (y : ι × E), ∥y.snd - x∥⁻¹ * ∥g y.snd - g x - (g' x) (y.snd - x)∥) (l.curry (𝓝 x)) (𝓝 0),
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
  have : (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (g' x) (a.snd - x))) =
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (f a.fst a.snd - f a.fst x))) +
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f a.fst a.snd - f a.fst x) -
      ((f' a.fst x) a.snd - (f' a.fst x) x))) +
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f' a.fst x - g' x) (a.snd - x))),
  { ext, simp only [pi.add_apply], rw [←smul_add, ←smul_add], congr,
  simp only [map_sub, sub_add_sub_cancel, continuous_linear_map.coe_sub', pi.sub_apply], },
  simp_rw this,
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0), simp only [add_zero],
  rw this,
  refine tendsto.add (tendsto.add _ _) _,
  simp only,
  { have := difference_quotients_converge_uniformly hf hfg hfg',
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
    have h1: tendsto (λ n : ι × E, g' n.snd - f' n.fst n.snd) (l ×ᶠ 𝓝 x) (𝓝 0),
    { rw metric.tendsto_uniformly_on_filter_iff at hfg',
      exact metric.tendsto_nhds.mpr (λ ε hε, by simpa using hfg' ε hε), },
    have h2: tendsto (λ n : ι, g' x - f' n x) l (𝓝 0),
    { rw metric.tendsto_nhds at h1 ⊢,
      exact (λ ε hε, (h1 ε hε).curry.mono (λ n hn, hn.self_of_nhds)), },
    have := (tendsto_fst.comp (h2.prod_map tendsto_id)),
    refine squeeze_zero_norm _ (tendsto_zero_iff_norm_tendsto_zero.mp this),
    intros n,
    simp_rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    by_cases hx : x = n.snd, { simp [hx], },
    have hnx : 0 < ∥n.snd - x∥,
    { rw norm_pos_iff, intros hx', exact hx (eq_of_sub_eq_zero hx').symm, },
    rw [inv_mul_le_iff hnx, mul_comm],
    simp only [function.comp_app, prod_map],
    rw norm_sub_rev,
    exact (f' n.fst x - g' x).le_op_norm (n.snd - x), },
end

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`. -/
lemma has_fderiv_at_of_tendsto_uniformly_on
  {s : set E} (hs : is_open s)
  (hf : ∀ (n : ι), ∀ (x : E), x ∈ s → has_fderiv_at (f n) (f' n x) x)
  (hfg : ∀ (x : E), x ∈ s → tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : tendsto_uniformly_on f' g' l s) :
  ∀ (x : E), x ∈ s → has_fderiv_at g (g' x) x :=
begin
  intros x hx,
  have hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd,
  { exact eventually_prod_iff.mpr ⟨(λ y, true), (by simp), (λ y, y ∈ s),
      eventually_mem_set.mpr (mem_nhds_iff.mpr ⟨s, rfl.subset, hs, hx⟩),
      (λ n hn y hy, hf n y hy)⟩, },

  have hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)),
  { exact eventually_iff.mpr (mem_nhds_iff.mpr ⟨s, set.subset_def.mpr hfg, hs, hx⟩), },

  have hfg' := hfg'.tendsto_uniformly_on_filter.mono_right (calc
    𝓝 x = 𝓝[s] x : ((hs.nhds_within_eq hx).symm)
    ... ≤ 𝓟 s : (by simp only [nhds_within, inf_le_right])),

  exact has_fderiv_at_of_tendsto_uniformly_on_filter hf hfg hfg',
end

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit. -/
lemma has_fderiv_at_of_tendsto_uniformly
  (hf : ∀ (n : ι), ∀ (x : E), has_fderiv_at (f n) (f' n x) x)
  (hfg : ∀ (x : E), tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : tendsto_uniformly f' g' l) :
  ∀ (x : E), has_fderiv_at g (g' x) x :=
begin
  intros x,
  have hf : ∀ (n : ι), ∀ (x : E), x ∈ set.univ → has_fderiv_at (f n) (f' n x) x, { simp [hf], },
  have hfg : ∀ (x : E), x ∈ set.univ → tendsto (λ n, f n x) l (𝓝 (g x)), { simp [hfg], },
  have hfg' : tendsto_uniformly_on f' g' l set.univ, { rwa tendsto_uniformly_on_univ, },
  refine has_fderiv_at_of_tendsto_uniformly_on is_open_univ hf hfg hfg' x (set.mem_univ x),
end

end limits_of_derivatives

section deriv

/-! ### `deriv` versions of above theorems -/

variables {ι : Type*} {l : filter ι} [ne_bot l]
  {𝕜 : Type*} [is_R_or_C 𝕜]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : ι → 𝕜 → G} {g : 𝕜 → G} {f' : ι → 𝕜 → G} {g' : 𝕜 → G}
  {x : 𝕜}

lemma uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_deriv
  (hf : ∀ᶠ (n : ι × 𝕜) in (l ×ᶠ 𝓝 x), has_deriv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : uniform_cauchy_seq_on_filter f' l (𝓝 x)) :
  uniform_cauchy_seq_on_filter f l (𝓝 x) :=
begin
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply
  -- `uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv`
  let F' : ι → 𝕜 → (𝕜 →L[𝕜] G) := (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)),
  simp_rw has_deriv_at_iff_has_fderiv_at at hf,
  have : ∀ n : ι, ∀ z : 𝕜, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z) = F' n z, simp,
  simp_rw this at hf,

  -- Now we need to rewrite hfg' in terms of continuous_linear_maps. The tricky part is that
  -- operator norms are written in terms of `≤` whereas metrics are written in terms of `<`. So we
  -- need to shrink `ε` utilizing the arhcimedian property of `ℝ`
  have hfg' : uniform_cauchy_seq_on_filter F' l (𝓝 x),
  { rw [normed_add_comm_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero,
      metric.tendsto_uniformly_on_filter_iff] at hfg' ⊢,
    intros ε hε,
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε.lt,
    apply (hfg' q hq).mono,
    intros n hn,
    refine lt_of_le_of_lt _ hq',
    simp only [F', dist_eq_norm, pi.zero_apply, zero_sub, norm_neg] at hn ⊢,
    refine continuous_linear_map.op_norm_le_bound _ hq.le _,
    intros z,
    simp only [continuous_linear_map.coe_sub', pi.sub_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply],
    rw [←smul_sub, norm_smul, mul_comm],
    exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le, },
  exact uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv hf hfg hfg',
end

lemma uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_deriv
  {r : ℝ} (hr : 0 < r)
  (hf : ∀ n : ι, ∀ y : 𝕜, y ∈ metric.ball x r → has_deriv_at (f n) (f' n y) y)
  (hfg : tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : uniform_cauchy_seq_on f' l (metric.ball x r)) :
  uniform_cauchy_seq_on f l (metric.ball x r) :=
begin
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply
  -- `uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv`
  let F' : ι → 𝕜 → (𝕜 →L[𝕜] G) := (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)),
  simp_rw has_deriv_at_iff_has_fderiv_at at hf,
  have : ∀ n : ι, ∀ z : 𝕜, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z) = F' n z, simp,
  simp_rw this at hf,

  -- Now we need to rewrite hfg' in terms of continuous_linear_maps. The tricky part is that
  -- operator norms are written in terms of `≤` whereas metrics are written in terms of `<`. So we
  -- need to shrink `ε` utilizing the arhcimedian property of `ℝ`
  have hfg' : uniform_cauchy_seq_on F' l (metric.ball x r),
  { rw [normed_add_comm_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero,
      metric.tendsto_uniformly_on_iff] at hfg' ⊢,
    intros ε hε,
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε.lt,
    apply (hfg' q hq).mono,
    intros n hn y hy,
    refine lt_of_le_of_lt _ hq',
    simp only [F', dist_eq_norm, pi.zero_apply, zero_sub, norm_neg] at hn ⊢,
    refine continuous_linear_map.op_norm_le_bound _ hq.le _,
    intros z,
    simp only [continuous_linear_map.coe_sub', pi.sub_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply],
    rw [←smul_sub, norm_smul, mul_comm],
    exact mul_le_mul (hn y hy).le rfl.le (norm_nonneg _) hq.le, },
  exact uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_fderiv hr hf hfg hfg',
end

lemma has_deriv_at_of_tendsto_uniformly_on_filter
  (hf : ∀ᶠ (n : ι × 𝕜) in (l ×ᶠ 𝓝 x), has_deriv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on_filter f' g' l (𝓝 x)) :
  has_deriv_at g (g' x) x :=
begin
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `has_fderiv_at_of_tendsto_uniformly_on_filter`
  let F' : ι → 𝕜 → (𝕜 →L[𝕜] G) := (λ n, λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)),
  let G' : 𝕜 → (𝕜 →L[𝕜] G) := (λ z, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (g' z)),

  simp_rw has_deriv_at_iff_has_fderiv_at at hf ⊢,
  have : ∀ z : 𝕜, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (g' z) = G' z, simp,
  rw this,
  have : ∀ n : ι, ∀ z : 𝕜, (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z) = F' n z, simp,
  simp_rw this at hf,

  -- Now we need to rewrite hfg' in terms of continuous_linear_maps. The tricky part is that
  -- operator norms are written in terms of `≤` whereas metrics are written in terms of `<`. So we
  -- need to shrink `ε` utilizing the arhcimedian property of `ℝ`
  have hfg' : tendsto_uniformly_on_filter F' G' l (𝓝 x),
  { rw metric.tendsto_uniformly_on_filter_iff at hfg' ⊢,
    intros ε hε,
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε.lt,
    apply (hfg' q hq).mono,
    intros n hn,
    refine lt_of_le_of_lt _ hq',
    simp only [F', G', dist_eq_norm] at hn ⊢,
    refine continuous_linear_map.op_norm_le_bound _ hq.le _,
    intros z,
    simp only [continuous_linear_map.coe_sub', pi.sub_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply],
    rw [←smul_sub, norm_smul, mul_comm],
    exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le, },
  exact has_fderiv_at_of_tendsto_uniformly_on_filter hf hfg hfg',
end

lemma has_deriv_at_of_tendsto_uniformly_on
  {s : set 𝕜} (hs : is_open s)
  (hf : ∀ (n : ι), ∀ (x : 𝕜), x ∈ s → has_deriv_at (f n) (f' n x) x)
  (hfg : ∀ (x : 𝕜), x ∈ s → tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : tendsto_uniformly_on f' g' l s) :
  ∀ (x : 𝕜), x ∈ s → has_deriv_at g (g' x) x :=
begin
  intros x hx,
  have hsx : s ∈ 𝓝 x, { exact mem_nhds_iff.mpr ⟨s, rfl.subset, hs, hx⟩, },
  rw tendsto_uniformly_on_iff_tendsto_uniformly_on_filter at hfg',
  have hfg' := hfg'.mono_right (le_principal_iff.mpr hsx),
  have hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)),
  { exact eventually_iff_exists_mem.mpr ⟨s, hsx, hfg⟩, },
  have hf : ∀ᶠ (n : ι × 𝕜) in (l ×ᶠ 𝓝 x), has_deriv_at (f n.fst) (f' n.fst n.snd) n.snd,
  { rw eventually_prod_iff,
    refine ⟨(λ y, true), by simp, (λ y, y ∈ s), _, (λ n hn y hy, hf n y hy)⟩,
    exact eventually_mem_set.mpr hsx, },
  exact has_deriv_at_of_tendsto_uniformly_on_filter hf hfg hfg',
end

lemma has_deriv_at_of_tendsto_uniformly
  (hf : ∀ (n : ι), ∀ (x : 𝕜), has_deriv_at (f n) (f' n x) x)
  (hfg : ∀ (x : 𝕜), tendsto (λ n, f n x) l (𝓝 (g x)))
  (hfg' : tendsto_uniformly f' g' l) :
  ∀ (x : 𝕜), has_deriv_at g (g' x) x :=
begin
  intros x,
  have hf : ∀ (n : ι), ∀ (x : 𝕜), x ∈ set.univ → has_deriv_at (f n) (f' n x) x, { simp [hf], },
  have hfg : ∀ (x : 𝕜), x ∈ set.univ → tendsto (λ n, f n x) l (𝓝 (g x)), { simp [hfg], },
  have hfg' : tendsto_uniformly_on f' g' l set.univ, { rwa tendsto_uniformly_on_univ, },
  exact has_deriv_at_of_tendsto_uniformly_on is_open_univ hf hfg hfg' x (set.mem_univ x),
end

end deriv
