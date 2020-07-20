/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.local_extr
import analysis.convex.topology

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `∥f x∥ ≤ B x` from upper estimates on `f'` or `∥f'∥`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `∥f x∥ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `∥f x - f a∥ ≤ C * ∥x - a∥`; several versions deal with
  right derivative and derivative within `[a, b]` (`has_deriv_within_at` or `deriv_within`).

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.mono_of_deriv_nonneg`, `convex.antimono_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_antimono_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/monotonically decreasing/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_mono`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `strict_fderiv_of_cont_diff` : a C^1 function over the reals is strictly differentiable.  (This
  is a corollary of the mean value inequality.)
-/


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set asymptotics continuous_linear_map filter
open_locale classical topological_space

/-! ### One-dimensional fencing inequalities -/

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in nhds_within x (Ioi x), (z - x)⁻¹ * (f z - f x) < r)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
begin
  change Icc a b ⊆ {x | f x ≤ B x},
  set s := {x | f x ≤ B x} ∩ Icc a b,
  have A : continuous_on (λ x, (f x, B x)) (Icc a b), from hf.prod hB,
  have : is_closed s,
  { simp only [s, inter_comm],
    exact A.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le' },
  apply this.Icc_subset_of_forall_exists_gt ha,
  rintros x ⟨hxB, xab⟩ y hy,
  change f x ≤ B x at hxB,
  cases lt_or_eq_of_le hxB with hxB hxB,
  { -- If `f x < B x`, then all we need is continuity of both sides
    apply @nonempty_of_mem_sets _ (nhds_within x (Ioi x)),
    refine inter_mem_sets _ (Ioc_mem_nhds_within_Ioi ⟨le_refl x, hy⟩),
    have : ∀ᶠ x in nhds_within x (Icc a b), f x < B x,
      from A x (Ico_subset_Icc_self xab)
        (mem_nhds_sets (is_open_lt continuous_fst continuous_snd) hxB),
    have : ∀ᶠ x in nhds_within x (Ioi x), f x < B x,
      from nhds_within_le_of_mem (Icc_mem_nhds_within_Ioi xab) this,
    refine mem_sets_of_superset this (set_of_subset_set_of.2 $ λ y, le_of_lt) },
  { rcases dense (bound x xab hxB) with ⟨r, hfr, hrB⟩,
    specialize hf' x xab r hfr,
    have HB : ∀ᶠ z in nhds_within x (Ioi x), r < (z - x)⁻¹ * (B z - B x),
      from (has_deriv_within_at_iff_tendsto_slope' $ lt_irrefl x).1 (hB' x xab)
        (mem_nhds_sets is_open_Ioi hrB),
    obtain ⟨z, ⟨hfz, hzB⟩, hz⟩ :
      ∃ z, ((z - x)⁻¹ * (f z - f x) < r ∧ r < (z - x)⁻¹ * (B z - B x)) ∧ z ∈ Ioc x y,
      from ((hf'.and_eventually HB).and_eventually
        (Ioc_mem_nhds_within_Ioi ⟨le_refl _, hy⟩)).exists,
    have := le_of_lt (lt_trans hfz hzB),
    refine ⟨z, _, hz⟩,
    rw [mul_le_mul_left (inv_pos.2 $ sub_pos.2 hz.1), hxB, sub_le_sub_iff_right] at this,
    exact this }
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in nhds_within x (Ioi x), (z - x)⁻¹ * (f z - f x) < r)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  -- `bound` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ B' x`
  (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r →
    ∃ᶠ z in nhds_within x (Ioi x), (z - x)⁻¹ * (f z - f x) < r) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
begin
  have Hr : ∀ x ∈ Icc a b, ∀ r ∈ Ioi (0:ℝ), f x ≤ B x + r * (x - a),
  { intros x hx r hr,
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound,
    { rwa [sub_self, mul_zero, add_zero] },
    { exact hB.add (continuous_on_const.mul
        (continuous_id.continuous_on.sub continuous_on_const)) },
    { assume x hx,
      exact (hB' x hx).add (((has_deriv_within_at_id x (Ioi x)).sub_const a).const_mul r) },
    { assume x hx _,
      rw [mul_one],
      exact (lt_add_iff_pos_right _).2 hr },
    exact hx },
  assume x hx,
  have : continuous_within_at (λ r, B x + r * (x - a)) (Ioi 0) 0,
    from continuous_within_at_const.add (continuous_within_at_id.mul continuous_within_at_const),
  convert continuous_within_at_const.closure_le _ this (Hr x hx); simp [closure_Ioi]
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' hf
  (λ x hx r hr, (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' $
assume x hx r hr, (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/

section

variables {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(∥f z∥ - ∥f x∥) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. -/
lemma image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*} [normed_group E]
  {f : ℝ → E} {f' : ℝ → ℝ} (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf ∥z - x∥⁻¹ * (∥f z∥ - ∥f x∥) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in nhds_within x (Ioi x), (z - x)⁻¹ * (∥f z∥ - ∥f x∥) < r)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuous_on hf) hf'
    ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ioi x) x)
  (bound : ∀ x ∈ Ico a b, ∥f' x∥ ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB' $
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_lt (bound x hx) hr))

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, ∥f' x∥ ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `∥f x - f a∥ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (bound : ∀x ∈ Ico a b, ∥f' x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  let g := λ x, f x - f a,
  have hg : continuous_on g (Icc a b), from hf.sub continuous_on_const,
  have hg' : ∀ x ∈ Ico a b, has_deriv_within_at g (f' x) (Ioi x) x,
  { assume x hx,
    simpa using (hf' x hx).sub (has_deriv_within_at_const _ _ _) },
  let B := λ x, C * (x - a),
  have hB : ∀ x, has_deriv_at B C x,
  { assume x,
    simpa using (has_deriv_at_const x C).mul ((has_deriv_at_id x).sub (has_deriv_at_const x a)) },
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound,
  { simp only [g, B] },
  { simp only [g, B], rw [sub_self, _root_.norm_zero, sub_self, mul_zero] }
end

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x ∈ Icc a b, has_deriv_within_at f (f' x) (Icc a b) x)
  (bound : ∀x ∈ Ico a b, ∥f' x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  refine norm_image_sub_le_of_norm_deriv_right_le_segment
    (λ x hx, (hf x hx).continuous_within_at) (λ x hx, _) bound,
  apply (hf x $ Ico_subset_Icc_self hx).nhds_within,
  exact Icc_mem_nhds_within_Ioi hx
end

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `deriv_within`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : differentiable_on ℝ f (Icc a b))
  (bound : ∀x ∈ Ico a b, ∥deriv_within f (Icc a b) x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  refine norm_image_sub_le_of_norm_deriv_le_segment' _ bound,
  exact λ x hx, (hf x  hx).has_deriv_within_at
end

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x ∈ Icc (0:ℝ) 1, has_deriv_within_at f (f' x) (Icc (0:ℝ) 1) x)
  (bound : ∀x ∈ Ico (0:ℝ) 1, ∥f' x∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
by simpa only [sub_zero, mul_one]
  using norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `deriv_within` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
  (hf : differentiable_on ℝ f (Icc (0:ℝ) 1))
  (bound : ∀x ∈ Ico (0:ℝ) 1, ∥deriv_within f (Icc (0:ℝ) 1) x∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
by simpa only [sub_zero, mul_one]
  using norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

end

/-! ### Vector-valued functions `f : E → F` -/

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le
  {f : E → F} {C : ℝ} {s : set E} {x y : E} {f' : E → (E →L[ℝ] F)}
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
begin
  /- By composition with `t ↦ x + t • (y-x)`, we reduce to a statement for functions defined
  on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
  We just have to check the differentiability of the composition and bounds on its derivative,
  which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_trans (norm_nonneg _) (bound x xs),
  set g : ℝ → E := λ t, x + t • (y - x),
  have Dg : ∀ t, has_deriv_at g (y-x) t,
  { assume t,
    simpa only [one_smul] using ((has_deriv_at_id t).smul_const (y - x)).const_add x },
  have segm : Icc 0 1 ⊆ g ⁻¹' s,
  { rw [← image_subset_iff, ← segment_eq_image'],
    apply hs.segment_subset xs ys },
  have : f x = f (g 0), by { simp only [g], rw [zero_smul, add_zero] },
  rw this,
  have : f y = f (g 1), by { simp only [g], rw [one_smul, add_sub_cancel'_right] },
  rw this,
  have D2: ∀ t ∈ Icc (0:ℝ) 1, has_deriv_within_at (f ∘ g)
    ((f' (g t) : E → F) (y-x)) (Icc (0:ℝ) 1) t,
  { intros t ht,
    exact (hf (g t) $ segm ht).comp_has_deriv_within_at _
      (Dg t).has_deriv_within_at segm },
  apply norm_image_sub_le_of_norm_deriv_le_segment_01' D2,
  assume t ht,
  refine le_trans (le_op_norm _ _) (mul_le_mul_of_nonneg_right _ (norm_nonneg _)),
  exact bound (g t) (segm $ Ico_subset_Icc_self ht)
end

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le {f : E → F} {C : ℝ} {s : set E} {x y : E}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥fderiv_within ℝ f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at)
bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le {f : E → F} {C : ℝ} {s : set E} {x y : E}
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) (bound : ∀x∈s, ∥fderiv ℝ f x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le
(λ x hx, (hf x hx).has_fderiv_at.has_fderiv_within_at) bound xs ys

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
  {f : E → F} {C : ℝ} {s : set E} {x y : E} {f' : E → (E →L[ℝ] F)} {φ : E →L[ℝ] F}
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
begin
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
  applies, `convex.norm_image_sub_le_of_norm_has_fderiv_within_le`. Then, we just need to glue
  together the pieces, expressing back `f` in terms of `g`. -/
  let g := λy, f y - φ y,
  have hg : ∀ x ∈ s, has_fderiv_within_at g (f' x - φ) s x :=
    λ x xs, (hf x xs).sub φ.has_fderiv_within_at,
  calc ∥f y - f x - φ (y - x)∥ = ∥f y - f x - (φ y - φ x)∥ : by simp
  ... = ∥(f y - φ y) - (f x - φ x)∥ : by abel
  ... = ∥g y - g x∥ : by simp
  ... ≤ C * ∥y - x∥ : convex.norm_image_sub_le_of_norm_has_fderiv_within_le hg bound hs xs ys,
end

/-- Variant of the mean value inequality on a convex set. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le' {f : E → F} {C : ℝ} {s : set E} {x y : E}
  {φ : E →L[ℝ] F} (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥fderiv_within ℝ f s x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (λ x hx, (hf x hx).has_fderiv_within_at)
bound xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le' {f : E → F} {C : ℝ} {s : set E} {x y : E}
  {φ : E →L[ℝ] F} (hf : ∀ x ∈ s, differentiable_at ℝ f x) (bound : ∀x∈s, ∥fderiv ℝ f x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le'
(λ x hx, (hf x hx).has_fderiv_at.has_fderiv_within_at) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem convex.is_const_of_fderiv_within_eq_zero {s : set E} (hs : convex s)
  {f : E → F} (hf : differentiable_on ℝ f s) (hf' : ∀ x ∈ s, fderiv_within ℝ f s x = 0)
  {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
have bound : ∀ x ∈ s, ∥fderiv_within ℝ f s x∥ ≤ 0,
  from λ x hx, by simp only [hf' x hx, _root_.norm_zero],
by simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm]
  using hs.norm_image_sub_le_of_norm_fderiv_within_le hf bound hx hy

theorem is_const_of_fderiv_eq_zero {f : E → F} (hf : differentiable ℝ f)
  (hf' : ∀ x, fderiv ℝ f x = 0) (x y : E) :
  f x = f y :=
convex_univ.is_const_of_fderiv_within_eq_zero hf.differentiable_on
  (λ x _, by rw fderiv_within_univ; exact hf' x) trivial trivial

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `has_deriv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_deriv_within_le
  {f f' : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
convex.norm_image_sub_le_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at)
(λ x hx, le_trans (by simp) (bound x hx)) hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv_within` -/
theorem convex.norm_image_sub_le_of_norm_deriv_within_le
  {f : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥deriv_within f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_deriv_within_le (λ x hx, (hf x hx).has_deriv_within_at)
bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem convex.norm_image_sub_le_of_norm_deriv_le {f : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) (bound : ∀x∈s, ∥deriv f x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_deriv_within_le
(λ x hx, (hf x hx).has_deriv_at.has_deriv_within_at) bound xs ys

/-! ### Functions `[a, b] → ℝ`. -/

section interval

-- Declare all variables here to make sure they come in a correct order
variables (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous_on f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hfd : differentiable_on ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : continuous_on g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hgd : differentiable_on ℝ g (Ioo a b))

include hab hfc hff' hgc hgg'

/-- Cauchy's Mean Value Theorem, `has_deriv_at` version. -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
begin
  let h := λ x, (g b - g a) * f x - (f b - f a) * g x,
  have hI : h a = h b,
  { simp only [h], ring },
  let h' := λ x, (g b - g a) * f' x - (f b - f a) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
    from λ x hx, ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a)),
  have hhc : continuous_on h (Icc a b),
    from (continuous_on_const.mul hfc).sub (continuous_on_const.mul hgc),
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

omit hgc hgg'

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff'
    id 1 continuous_id.continuous_on (λ x hx, has_deriv_at_id x) with ⟨c, cmem, hc⟩,
  use [c, cmem],
  simp only [_root_.id, pi.one_apply, mul_one] at hc,
  rw [← hc, mul_div_cancel_left],
  exact ne_of_gt (sub_pos.2 hab)
end

omit hff'

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
lemma exists_ratio_deriv_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * (deriv f c) = (f b - f a) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)
  g (deriv g) hgc (λ x hx, ((hgd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)

/-- Lagrange's Mean Value Theorem, `deriv` version. -/
lemma exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_has_deriv_at_eq_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)

end interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.mul_sub_lt_image_sub_of_lt_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
  ∀ x y ∈ D, x < y → C * (y - x) < f y - f x :=
begin
  assume x y hx hy hxy,
  have hxyD : Icc x y ⊆ D, from convex_real_iff.1 hD hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  have : C < (f y - f x) / (y - x), by { rw [← ha], exact hf'_gt _ (hxyD' a_mem) },
  exact (lt_div_iff (sub_pos.2 hxy)).1 this
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) :
  C * (y - x) < f y - f x :=
convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_gt x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.mul_sub_le_image_sub_of_le_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → C * (y - x) ≤ f y - f x :=
begin
  assume x y hx hy hxy,
  cases eq_or_lt_of_le hxy with hxy' hxy', by rw [hxy', sub_self, sub_self, mul_zero],
  have hxyD : Icc x y ⊆ D, from convex_real_iff.1 hD hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD'),
  have : C ≤ (f y - f x) / (y - x), by { rw [← ha], exact hf'_ge _ (hxyD' a_mem) },
  exact (le_div_iff (sub_pos.2 hxy')).1 this
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) :
  C * (y - x) ≤ f y - f x :=
convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_ge x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.image_sub_lt_mul_sub_of_deriv_lt {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (lt_hf' : ∀ x ∈ interior D, deriv f x < C) :
  ∀ x y ∈ D, x < y → f y - f x < C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv.neg, neg_lt_neg_iff],
    exact lt_hf' x hx },
  simpa [-neg_lt_neg_iff]
    using neg_lt_neg (hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x y hx hy hxy)
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) :
  f y - f x < C * (y - x) :=
convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuous_on hf.differentiable_on
  (λ x _, lt_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.image_sub_le_mul_sub_of_deriv_le {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) :
  ∀ x y ∈ D, x ≤ y → f y - f x ≤ C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv.neg, neg_le_neg_iff],
    exact le_hf' x hx },
  simpa [-neg_le_neg_iff]
    using neg_le_neg (hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x y hx hy hxy)
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) :
  f y - f x ≤ C * (y - x) :=
convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuous_on hf.differentiable_on
  (λ x _, le_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotonically increasing function on `D`. -/
theorem convex.strict_mono_of_deriv_pos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_pos : ∀ x ∈ interior D, 0 < deriv f x) :
  ∀ x y ∈ D, x < y → f x < f y :=
by simpa only [zero_mul, sub_pos] using hD.mul_sub_lt_image_sub_of_lt_deriv hf hf' hf'_pos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotonically increasing function. -/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf'_pos : ∀ x, 0 < deriv f x) :
  strict_mono f :=
λ x y hxy, convex_univ.strict_mono_of_deriv_pos hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_pos x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotonically increasing function on `D`. -/
theorem convex.mono_of_deriv_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → f x ≤ f y :=
by simpa only [zero_mul, sub_nonneg] using hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotonically increasing function. -/
theorem mono_of_deriv_nonneg {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
  monotone f :=
λ x y hxy, convex_univ.mono_of_deriv_nonneg hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly monotonically decreasing function on `D`. -/
theorem convex.strict_antimono_of_deriv_neg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_neg : ∀ x ∈ interior D, deriv f x < 0) :
  ∀ x y ∈ D, x < y → f y < f x :=
by simpa only [zero_mul, sub_lt_zero] using hD.image_sub_lt_mul_sub_of_deriv_lt hf hf' hf'_neg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly monotonically decreasing function. -/
theorem strict_antimono_of_deriv_neg {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf' : ∀ x, deriv f x < 0) :
  ∀ ⦃x y⦄, x < y → f y < f x :=
λ x y hxy, convex_univ.strict_antimono_of_deriv_neg hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is a monotonically decreasing function on `D`. -/
theorem convex.antimono_of_deriv_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) :
  ∀ x y ∈ D, x ≤ y → f y ≤ f x :=
by simpa only [zero_mul, sub_nonpos] using hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is a monotonically decreasing function. -/
theorem antimono_of_deriv_nonpos {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
  ∀ ⦃x y⦄, x ≤ y → f y ≤ f x :=
λ x y hxy, convex_univ.antimono_of_deriv_nonpos hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv_mono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_mono : ∀ x y ∈ interior D, x ≤ y → deriv f x ≤ deriv f y) :
  convex_on D f :=
convex_on_real_of_slope_mono_adjacent hD
begin
  intros x y z hx hz hxy hyz,
  -- First we prove some trivial inclusions
  have hxzD : Icc x z ⊆ D, from convex_real_iff.1 hD hx hz,
  have hxyD : Icc x y ⊆ D, from subset.trans (Icc_subset_Icc_right $ le_of_lt hyz) hxzD,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  have hyzD : Icc y z ⊆ D, from subset.trans (Icc_subset_Icc_left $ le_of_lt hxy) hxzD,
  have hyzD' : Ioo y z ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩,
  -- Then we apply MVT to both `[x, y]` and `[y, z]`
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y),
    from exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD'),
  rw [← ha, ← hb],
  exact hf'_mono a b (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (le_of_lt $ lt_trans hay hyb)
end

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv_mono {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf'_mono : monotone (deriv f)) : convex_on univ f :=
convex_on_of_deriv_mono convex_univ hf.continuous.continuous_on hf.differentiable_on
  (λ x y _ _ h, hf'_mono h)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its interior,
and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'' : differentiable_on ℝ (deriv f) (interior D))
  (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ (deriv^[2] f x)) :
  convex_on D f :=
convex_on_of_deriv_mono hD hf hf' $
assume x y hx hy hxy,
hD.interior.mono_of_deriv_nonneg hf''.continuous_on (by rwa [interior_interior])
  (by rwa [interior_interior]) _ _ hx hy hxy

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : differentiable ℝ f)
  (hf'' : differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f x)) :
  convex_on univ f :=
convex_on_of_deriv2_nonneg convex_univ hf'.continuous.continuous_on hf'.differentiable_on
  hf''.differentiable_on (λ x _, hf''_nonneg x)

/-! ### Functions `f : E → ℝ` -/

/-- Lagrange's Mean Value Theorem, applied to convex domains. -/
theorem domain_mvt
  {f : E → ℝ} {s : set E} {x y : E} {f' : E → (E →L[ℝ] ℝ)}
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) :
  ∃ z ∈ segment x y, f y - f x = f' z (y - x) :=
begin
  have hIccIoo := @Ioo_subset_Icc_self ℝ _ 0 1,
-- parametrize segment
  set g : ℝ → E := λ t, x + t • (y - x),
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, g t ∈ segment x y,
  { rw segment_eq_image',
    simp only [mem_image, and_imp, add_right_inj],
    intros t ht, exact ⟨t, ht, rfl⟩ },
  have hseg' : Icc 0 1 ⊆ g ⁻¹' s,
  { rw ← image_subset_iff, unfold image, change ∀ _, _,
    intros z Hz, rw mem_set_of_eq at Hz, rcases Hz with ⟨t, Ht, hgt⟩,
    rw ← hgt, exact hs.segment_subset xs ys (hseg t Ht) },
-- derivative of pullback of f under parametrization
  have hfg: ∀ t ∈ Icc (0:ℝ) 1, has_deriv_within_at (f ∘ g)
    ((f' (g t) : E → ℝ) (y-x)) (Icc (0:ℝ) 1) t,
  { intros t Ht,
    have hg : has_deriv_at g (y-x) t,
    { have := ((has_deriv_at_id t).smul_const (y - x)).const_add x,
      rwa one_smul at this },
    exact (hf (g t) $ hseg' Ht).comp_has_deriv_within_at _ hg.has_deriv_within_at hseg' },
-- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ (t ∈ Ioo (0:ℝ) 1), ((f' (g t) : E → ℝ) (y-x)) = (f (g 1) - f (g 0)) / (1 - 0),
  { refine exists_has_deriv_at_eq_slope (f ∘ g) _ (by norm_num) _ _,
    { unfold continuous_on,
      exact λ t Ht, (hfg t Ht).continuous_within_at },
    { refine λ t Ht, (hfg t $ hIccIoo Ht).has_deriv_at _,
      refine mem_nhds_sets_iff.mpr _,
      use (Ioo (0:ℝ) 1),
      refine ⟨hIccIoo, _, Ht⟩,
      simp [real.Ioo_eq_ball, is_open_ball] } },
-- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩,
  use g t, refine ⟨hseg t $ hIccIoo Ht, _⟩,
  simp [g, hMVT'],
end

/-! ### Vector-valued functions `f : E → F`.  Strict differentiability. -/

/-- Over the reals, a continuously differentiable function is strictly differentiable. -/
lemma strict_fderiv_of_cont_diff
  {f : E → F} {s : set E}  {x : E} {f' : E → (E →L[ℝ] F)}
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (hcont : continuous_on f' s) (hs : s ∈ 𝓝 x) :
  has_strict_fderiv_at f (f' x) x :=
begin
-- turn little-o definition of strict_fderiv into an epsilon-delta statement
  apply is_o_iff_forall_is_O_with.mpr,
  intros c hc,
  refine is_O_with.of_bound (eventually_iff.mpr (mem_nhds_iff.mpr _)),
-- the correct ε is the modulus of continuity of f', shrunk to be inside s
  rcases (metric.continuous_on_iff.mp hcont x (mem_of_nhds hs) c hc) with ⟨ε₁, H₁, hcont'⟩,
  rcases (mem_nhds_iff.mp hs) with ⟨ε₂, H₂, hε₂⟩,
  refine ⟨min ε₁ ε₂, lt_min H₁ H₂, _⟩,
-- mess with ε construction
  set t := ball x (min ε₁ ε₂),
  have hts : t ⊆ s := λ _ hy, hε₂ (ball_subset_ball (min_le_right ε₁ ε₂) hy),
  have Hf : ∀ y ∈ t, has_fderiv_within_at f (f' y) t y :=
    λ y yt, has_fderiv_within_at.mono (hf y (hts yt)) hts,
  have hconv := convex_ball x (min ε₁ ε₂),
-- simplify formulas involving the product E × E
  rintros ⟨a, b⟩ h,
  simp only [mem_set_of_eq, map_sub],
  have hab : a ∈ t ∧ b ∈ t := by rwa [mem_ball, prod.dist_eq, max_lt_iff] at h,
-- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀ x' ∈ t, ∥f' x' - f' x∥ ≤ c,
  { intros x' H',
    refine le_of_lt (hcont' x' (hts H') _),
    exact ball_subset_ball (min_le_left ε₁ ε₂) H' },
-- apply mean value theorem
  simpa using convex.norm_image_sub_le_of_norm_has_fderiv_within_le' Hf hf' hconv hab.2 hab.1,
end
