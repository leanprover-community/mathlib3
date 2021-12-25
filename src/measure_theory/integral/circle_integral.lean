/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.integral.interval_integral
import analysis.normed_space.pointwise
import analysis.special_functions.non_integrable
import analysis.analytic.basic

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space with second countable topology. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `circle_map c R`: the exponential map $θ ↦ c + R e^{θi}$;

* `circle_integrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circle_map c R` is integrable on `[0, 2π]`;

* `circle_integral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchy_power_series f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circle_map c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `metric.closed_ball c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `has_fpower_series_on_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchy_power_series f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `metric.ball c R`;

* `circle_integral.integral_sub_zpow_of_undef`, `circle_integral.integral_sub_zpow_of_ne`, and
  `circle_integral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circle_integral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circle_integral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circle_integral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see #10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/

variables {E : Type*} [measurable_space E] [normed_group E]

noncomputable theory

open_locale real nnreal interval pointwise topological_space
open complex measure_theory topological_space metric function set filter asymptotics

/-!
### `circle_map`, a parametrization of a circle
-/

/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circle_map (c : ℂ) (R : ℝ) : ℝ → ℂ := λ θ, c + R * exp (θ * I)

/-- `circle_map` is `2π`-periodic. -/
lemma periodic_circle_map (c : ℂ) (R : ℝ) : periodic (circle_map c R) (2 * π) :=
λ θ, by simp [circle_map, add_mul, exp_periodic _]

@[simp] lemma circle_map_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) :
  circle_map c R θ - c = circle_map 0 R θ :=
by simp [circle_map]

@[simp] lemma abs_circle_map_zero (R : ℝ) (θ : ℝ) : abs (circle_map 0 R θ) = |R| :=
by simp [circle_map]

lemma circle_map_mem_sphere' (c : ℂ) (R : ℝ) (θ : ℝ) : circle_map c R θ ∈ sphere c (|R|) :=
by simp

lemma circle_map_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : circle_map c R θ ∈ sphere c R :=
by simpa only [_root_.abs_of_nonneg hR] using circle_map_mem_sphere' c R θ

lemma circle_map_mem_closed_ball (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
  circle_map c R θ ∈ closed_ball c R :=
sphere_subset_closed_ball (circle_map_mem_sphere c hR θ)

/-- The range of `circle_map c R` is the circle with center `c` and radius `|R|`. -/
@[simp] lemma range_circle_map (c : ℂ) (R : ℝ) : range (circle_map c R) = sphere c (|R|) :=
calc range (circle_map c R) = c +ᵥ R • range (λ θ : ℝ, exp (θ * I)) :
  by simp only [← image_vadd, ← image_smul, ← range_comp, vadd_eq_add, circle_map, (∘), real_smul]
... = sphere c (|R|) : by simp [smul_sphere R (0 : ℂ) zero_le_one, real.norm_eq_abs]

/-- The image of `(0, 2π]` under `circle_map c R` is the circle with center `c` and radius `|R|`. -/
@[simp] lemma image_circle_map_Ioc (c : ℂ) (R : ℝ) :
  circle_map c R '' Ioc 0 (2 * π) = sphere c (|R|) :=
by rw [← range_circle_map, ← (periodic_circle_map c R).image_Ioc real.two_pi_pos 0, zero_add]

@[simp] lemma circle_map_eq_center_iff {c : ℂ} {R : ℝ} {θ : ℝ} : circle_map c R θ = c ↔ R = 0 :=
by simp [circle_map, exp_ne_zero]

@[simp] lemma circle_map_zero_radius (c : ℂ) : circle_map c 0 = const ℝ c :=
funext $ λ θ, circle_map_eq_center_iff.2 rfl

lemma circle_map_ne_center {c : ℂ} {R : ℝ} (hR : R ≠ 0) {θ : ℝ} : circle_map c R θ ≠ c :=
mt circle_map_eq_center_iff.1 hR

lemma has_deriv_at_circle_map (c : ℂ) (R : ℝ) (θ : ℝ) :
  has_deriv_at (circle_map c R) (circle_map 0 R θ * I) θ :=
by simpa only [mul_assoc, one_mul, of_real_clm_apply, circle_map, of_real_one, zero_add]
 using ((of_real_clm.has_deriv_at.mul_const I).cexp_real.const_mul (R : ℂ)).const_add c

/- TODO: prove `times_cont_diff ℝ (circle_map c R)`. This needs a version of `times_cont_diff.mul`
for multiplication in a normed algebra over the base field. -/

lemma differentiable_circle_map (c : ℂ) (R : ℝ) :
  differentiable ℝ (circle_map c R) :=
λ θ, (has_deriv_at_circle_map c R θ).differentiable_at

@[continuity] lemma continuous_circle_map (c : ℂ) (R : ℝ) : continuous (circle_map c R) :=
(differentiable_circle_map c R).continuous

@[measurability] lemma measurable_circle_map (c : ℂ) (R : ℝ) : measurable (circle_map c R) :=
(continuous_circle_map c R).measurable

@[simp] lemma deriv_circle_map (c : ℂ) (R : ℝ) (θ : ℝ) :
  deriv (circle_map c R) θ = circle_map 0 R θ * I :=
(has_deriv_at_circle_map _ _ _).deriv

lemma deriv_circle_map_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} :
  deriv (circle_map c R) θ = 0 ↔ R = 0 :=
by simp [I_ne_zero]

lemma deriv_circle_map_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) :
  deriv (circle_map c R) θ ≠ 0 :=
mt deriv_circle_map_eq_zero_iff.1 hR

lemma lipschitz_with_circle_map (c : ℂ) (R : ℝ) :
  lipschitz_with R.nnabs (circle_map c R) :=
lipschitz_with_of_nnnorm_deriv_le (differentiable_circle_map _ _) $ λ θ,
  nnreal.coe_le_coe.1 $ by simp

/-!
### Integrability of a function on a circle
-/

/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circle_map c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circle_integral` is
`(deriv (circle_map c R) θ) • f (circle_map c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circle_map c R` whenever `R ≠ 0`. -/
def circle_integrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
interval_integrable (λ θ : ℝ, f (circle_map c R θ)) volume 0 (2 * π)

@[simp] lemma circle_integrable_const (a : E) (c : ℂ) (R : ℝ) :
  circle_integrable (λ _, a) c R :=
interval_integrable_const

namespace circle_integrable

variables {f g : ℂ → E} {c : ℂ} {R : ℝ}

lemma add [borel_space E] [second_countable_topology E]
  (hf : circle_integrable f c R) (hg : circle_integrable g c R) :
  circle_integrable (f + g) c R :=
hf.add hg

lemma neg [borel_space E] (hf : circle_integrable f c R) : circle_integrable (-f) c R := hf.neg

/-- The function we actually integrate over `[0, 2π]` in the definition of `circle_integral` is
integrable. -/
lemma out [borel_space E] [normed_space ℂ E] [second_countable_topology E]
  (hf : circle_integrable f c R) :
  interval_integrable (λ θ : ℝ, deriv (circle_map c R) θ • f (circle_map c R θ)) volume 0 (2 * π) :=
begin
  simp only [circle_integrable, deriv_circle_map, interval_integrable_iff] at *,
  refine (hf.norm.const_mul (|R|)).mono' _ _,
  { exact (((continuous_circle_map _ _).ae_measurable _).mul_const I).smul hf.ae_measurable },
  { simp [norm_smul] }
end

end circle_integrable

@[simp] lemma circle_integrable_zero_radius {f : ℂ → E} {c : ℂ} : circle_integrable f c 0 :=
by simp [circle_integrable]

lemma circle_integrable_iff [borel_space E] [normed_space ℂ E] [second_countable_topology E]
  {f : ℂ → E} {c : ℂ} {R : ℝ} (h₀ : R ≠ 0) : circle_integrable f c R ↔
  interval_integrable (λ θ : ℝ, deriv (circle_map c R) θ • f (circle_map c R θ)) volume 0 (2 * π) :=
begin
  refine ⟨λ h, h.out, λ h, _⟩,
  simp only [circle_integrable, interval_integrable_iff, deriv_circle_map] at h ⊢,
  refine (h.norm.const_mul (|R|⁻¹)).mono' _ _,
  { have H : ∀ {θ}, circle_map 0 R θ * I ≠ 0 := λ θ, by simp [h₀, I_ne_zero],
    simpa only [inv_smul_smul₀ H]
      using (((continuous_circle_map 0 R).ae_measurable _).mul_const I).inv.smul h.ae_measurable },
  { simp [norm_smul, h₀] },
end

lemma continuous_on.circle_integrable' [borel_space E] {f : ℂ → E} {c : ℂ} {R : ℝ}
  (hf : continuous_on f (sphere c (|R|))) :
  circle_integrable f c R :=
(hf.comp_continuous (continuous_circle_map _ _)
  (circle_map_mem_sphere' _ _)).interval_integrable _ _

lemma continuous_on.circle_integrable [borel_space E] {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
  (hf : continuous_on f (sphere c R)) :
  circle_integrable f c R :=
continuous_on.circle_integrable' $ (_root_.abs_of_nonneg hR).symm ▸ hf

/-- The function `λ z, (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c` and
radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp] lemma circle_integrable_sub_zpow_iff {c w : ℂ} {R : ℝ} {n : ℤ} :
  circle_integrable (λ z, (z - w) ^ n) c R ↔ R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c (|R|) :=
begin
  split,
  { intro h, contrapose! h, rcases h with ⟨hR, hn, hw⟩,
    simp only [circle_integrable_iff hR, deriv_circle_map],
    rw ← image_circle_map_Ioc at hw, rcases hw with ⟨θ, hθ, rfl⟩,
    replace hθ : θ ∈ [0, 2 * π], from Icc_subset_interval (Ioc_subset_Icc_self hθ),
    refine not_interval_integrable_of_sub_inv_is_O_punctured _ real.two_pi_pos.ne hθ,
    set f : ℝ → ℂ := λ θ', circle_map c R θ' - circle_map c R θ,
    have : ∀ᶠ θ' in 𝓝[≠] θ, f θ' ∈ ball (0 : ℂ) 1 \ {0},
    { suffices : ∀ᶠ z in 𝓝[≠] (circle_map c R θ), z - circle_map c R θ ∈ ball (0 : ℂ) 1 \ {0},
        from ((differentiable_circle_map c R θ).has_deriv_at.tendsto_punctured_nhds
          (deriv_circle_map_ne_zero hR)).eventually this,
      filter_upwards [self_mem_nhds_within,
        mem_nhds_within_of_mem_nhds (ball_mem_nhds _ zero_lt_one)],
      simp [dist_eq, sub_eq_zero] { contextual := tt } },
    refine ((((has_deriv_at_circle_map c R θ).is_O_sub).mono inf_le_left).inv_rev
      (this.mono (λ θ', and.right))).trans _,
    refine is_O.of_bound (|R|)⁻¹ (this.mono $ λ θ' hθ', _),
    set x := abs (f θ'),
    suffices : x⁻¹ ≤ x ^ n, by simpa [inv_mul_cancel_left₀, mt _root_.abs_eq_zero.1 hR],
    have : x ∈ Ioo (0 : ℝ) 1, by simpa [and.comm, x] using hθ',
    rw ← zpow_neg_one,
    refine (zpow_strict_anti this.1 this.2).le_iff_le.2 (int.lt_add_one_iff.1 _), exact hn },
  { rintro (rfl|H),
    exacts [circle_integrable_zero_radius,
      ((continuous_on_id.sub continuous_on_const).zpow _ $ λ z hz, H.symm.imp_left $
        λ hw, sub_ne_zero.2 $ ne_of_mem_of_not_mem hz hw).circle_integrable'] },
end

@[simp] lemma circle_integrable_sub_inv_iff {c w : ℂ} {R : ℝ} :
  circle_integrable (λ z, (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ sphere c (|R|) :=
by { simp only [← zpow_neg_one, circle_integrable_sub_zpow_iff], norm_num }

variables [normed_space ℂ E] [complete_space E] [borel_space E] [second_countable_topology E]

/-- Definition for $\oint_{|z-c|=R} f(z)\,dz$. -/
def circle_integral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
∫ (θ : ℝ) in 0..2 * π, deriv (circle_map c R) θ • f (circle_map c R θ)

notation `∮` binders ` in ` `C(` c `, ` R `)` `, ` r:(scoped:60 f, circle_integral f c R) := r

namespace circle_integral

@[simp] lemma integral_radius_zero (f : ℂ → E) (c : ℂ) : ∮ z in C(c, 0), f z = 0 :=
by simp [circle_integral]

lemma integral_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : eq_on f g (sphere c R)) :
  ∮ z in C(c, R), f z = ∮ z in C(c, R), g z :=
interval_integral.integral_congr $ λ θ hθ, by simp only [h (circle_map_mem_sphere _ hR _)]

lemma integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬circle_integrable f c R) :
  ∮ z in C(c, R), f z = 0 :=
begin
  rcases eq_or_ne R 0 with rfl|h0, { simp },
  exact interval_integral.integral_undef (mt (circle_integrable_iff h0).mpr hf)
end

lemma integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : circle_integrable f c R)
  (hg : circle_integrable g c R) :
  ∮ z in C(c, R), f z - g z = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z :=
by simp only [circle_integral, smul_sub, interval_integral.integral_sub hf.out hg.out]

lemma norm_integral_le_of_norm_le_const' {f : ℂ → E} {c : ℂ} {R C : ℝ}
  (hf : ∀ z ∈ sphere c (|R|), ∥f z∥ ≤ C) :
  ∥∮ z in C(c, R), f z∥ ≤ 2 * π * |R| * C :=
calc ∥∮ z in C(c, R), f z∥ ≤ |R| * C * |2 * π - 0| :
  interval_integral.norm_integral_le_of_norm_le_const $ λ θ _,
    (calc ∥deriv (circle_map c R) θ • f (circle_map c R θ)∥ = |R| * ∥f (circle_map c R θ)∥ :
      by simp [norm_smul]
    ... ≤ |R| * C : mul_le_mul_of_nonneg_left (hf _ $ circle_map_mem_sphere' _ _ _)
      (_root_.abs_nonneg _))
... = 2 * π * |R| * C :
  by { rw [sub_zero, _root_.abs_of_pos real.two_pi_pos], ac_refl }

lemma norm_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
  (hf : ∀ z ∈ sphere c R, ∥f z∥ ≤ C) :
  ∥∮ z in C(c, R), f z∥ ≤ 2 * π * R * C :=
have |R| = R, from _root_.abs_of_nonneg hR,
calc ∥∮ z in C(c, R), f z∥ ≤ 2 * π * |R| * C :
  norm_integral_le_of_norm_le_const' $ by rwa this
... = 2 * π * R * C : by rw this

@[simp] lemma integral_smul {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] [smul_comm_class 𝕜 ℂ E]
  (a : 𝕜) (f : ℂ → E) (c : ℂ) (R : ℝ) :
  ∮ z in C(c, R), a • f z = a • ∮ z in C(c, R), f z :=
by simp only [circle_integral, ← smul_comm a, interval_integral.integral_smul]

@[simp] lemma integral_smul_const (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
  ∮ z in C(c, R), (f z • a) = (∮ z in C(c, R), f z) • a :=
by simp only [circle_integral, interval_integral.integral_smul_const, ← smul_assoc]

@[simp] lemma integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
  ∮ z in C(c, R), a * f z = a * ∮ z in C(c, R), f z :=
integral_smul a f c R

@[simp] lemma integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
  ∮ z in C(c, R), (z - c)⁻¹ = 2 * π * I :=
by simp [circle_integral, ← div_eq_mul_inv, mul_div_cancel_left _ (circle_map_ne_center hR)]

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`. -/
lemma integral_eq_zero_of_has_deriv_within_at' {f f' : ℂ → E} {c : ℂ} {R : ℝ}
  (h : ∀ z ∈ sphere c (|R|), has_deriv_within_at f (f' z) (sphere c (|R|)) z) :
  ∮ z in C(c, R), f' z = 0 :=
begin
  by_cases hi : circle_integrable f' c R,
  { rw ← sub_eq_zero.2 ((periodic_circle_map c R).comp f).eq,
    refine interval_integral.integral_eq_sub_of_has_deriv_at (λ θ hθ, _) hi.out,
    exact (h _ (circle_map_mem_sphere' _ _ _)).scomp_has_deriv_at θ
      (differentiable_circle_map _ _ _).has_deriv_at (circle_map_mem_sphere' _ _) },
  { exact integral_undef hi }
end

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`. -/
lemma integral_eq_zero_of_has_deriv_within_at {f f' : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
  (h : ∀ z ∈ sphere c R, has_deriv_within_at f (f' z) (sphere c R) z) :
  ∮ z in C(c, R), f' z = 0 :=
integral_eq_zero_of_has_deriv_within_at' $ (_root_.abs_of_nonneg hR).symm.subst h

/-- If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on the circle with
center `c` and radius `(|R|)`, so the integral `∮ z in C(c, R), (z - w) ^ n` is equal to zero. -/
lemma integral_sub_zpow_of_undef {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0) (hw : w ∈ sphere c (|R|)) :
  ∮ z in C(c, R), (z - w) ^ n = 0 :=
begin
  rcases eq_or_ne R 0 with rfl|h0, { apply integral_radius_zero },
  apply integral_undef,
  simp [circle_integrable_sub_zpow_iff, *]
end

/-- If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
lemma integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
  ∮ z in C(c, R), (z - w) ^ n = 0 :=
begin
  rcases em (w ∈ sphere c (|R|) ∧ n < -1) with ⟨hw, hn⟩|H,
  { exact integral_sub_zpow_of_undef (hn.trans dec_trivial) hw },
  push_neg at H,
  have hd : ∀ z, (z ≠ w ∨ -1 ≤ n) → has_deriv_at (λ z, (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z,
  { intros z hne,
    convert ((has_deriv_at_zpow (n + 1) _ (hne.imp _ _)).comp z
      ((has_deriv_at_id z).sub_const w)).div_const _ using 1,
    { have hn' : (n + 1 : ℂ) ≠ 0,
        by rwa [ne, ← eq_neg_iff_add_eq_zero, ← int.cast_one, ← int.cast_neg, int.cast_inj],
      simp [mul_assoc, mul_div_cancel_left _ hn'] },
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1] },
  refine integral_eq_zero_of_has_deriv_within_at' (λ z hz, (hd z _).has_deriv_within_at),
  exact (ne_or_eq z w).imp_right (λ h, H $ h ▸ hz)
end

end circle_integral

/-- The power series that is equal to
$\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circle_map c R`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `metric.closed_ball c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `f`, this power
series converges to the Cauchy integral for `f`. -/
def cauchy_power_series (f : ℂ → E) (c : ℂ) (R : ℝ) :
  formal_multilinear_series ℂ ℂ E :=
λ n, continuous_multilinear_map.mk_pi_field ℂ _ $
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z

lemma cauchy_power_series_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ) :
  cauchy_power_series f c R n (λ _, w) =
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z :=
by simp only [cauchy_power_series, continuous_multilinear_map.mk_pi_field_apply, fin.prod_const,
  div_eq_mul_inv, mul_pow, mul_smul, circle_integral.integral_smul, ← smul_comm (w ^ n)]

lemma norm_cauchy_power_series_le (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) :
  ∥cauchy_power_series f c R n∥ ≤
    (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map c R θ)∥) * (|R|⁻¹) ^ n :=
calc ∥cauchy_power_series f c R n∥
    = (2 * π)⁻¹ * ∥∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z∥ :
  by simp [cauchy_power_series, norm_smul, real.pi_pos.le]
... ≤ (2 * π)⁻¹ * ∫ θ in 0..2*π, ∥deriv (circle_map c R) θ • (circle_map c R θ - c)⁻¹ ^ n •
  (circle_map c R θ - c)⁻¹ • f (circle_map c R θ)∥ :
  mul_le_mul_of_nonneg_left (interval_integral.norm_integral_le_integral_norm real.two_pi_pos.le)
    (by simp [real.pi_pos.le])
... = (2 * π)⁻¹ * (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ (x : ℝ) in 0..2 * π, ∥f (circle_map c R x)∥))) :
  by simp [norm_smul, mul_left_comm (|R|)]
... ≤ (2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map c R θ)∥) * |R|⁻¹ ^ n :
  begin
    rcases eq_or_ne R 0 with rfl|hR,
    { cases n; simp [real.two_pi_pos] },
    { rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)],
      rwa [ne.def, _root_.abs_eq_zero] }
  end

lemma le_radius_cauchy_power_series (f : ℂ → E) (c : ℂ) (R : ℝ≥0) :
  ↑R ≤ (cauchy_power_series f c R).radius :=
begin
  refine (cauchy_power_series f c R).le_radius_of_bound
    ((2 * π)⁻¹ * (∫ θ : ℝ in 0..2*π, ∥f (circle_map c R θ)∥)) (λ n, _),
  refine (mul_le_mul_of_nonneg_right (norm_cauchy_power_series_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans _,
  rw [_root_.abs_of_nonneg R.coe_nonneg],
  cases eq_or_ne (R ^ n : ℝ) 0 with hR hR,
  { rw [hR, mul_zero],
    exact mul_nonneg (inv_nonneg.2 real.two_pi_pos.le)
      (interval_integral.integral_nonneg real.two_pi_pos.le (λ _ _, norm_nonneg _)) },
  { rw [inv_pow₀, inv_mul_cancel_right₀ hR] }
end

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc
`metric.ball c R`. -/
lemma has_sum_two_pi_I_cauchy_power_series_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
  (hf : circle_integrable f c R) (hw : abs w < R) :
  has_sum (λ n : ℕ, ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z)
    (∮ z in C(c, R), (z - (c + w))⁻¹ • f z) :=
begin
  have hR : 0 < R := (abs_nonneg w).trans_lt hw,
  have hwR : abs w / R ∈ Ico (0 : ℝ) 1,
    from ⟨div_nonneg (abs_nonneg w) hR.le, (div_lt_one hR).2 hw⟩,
  refine interval_integral.has_sum_integral_of_dominated_convergence
    (λ n θ, ∥f (circle_map c R θ)∥ * (abs w / R) ^ n) (λ n, _) (λ n, _) _ _ _,
  { simp only [deriv_circle_map], have := hf.def.1, measurability },
  { simp [norm_smul, abs_of_pos hR, mul_left_comm R, mul_inv_cancel_left₀ hR.ne', mul_comm (∥_∥)] },
  { exact eventually_of_forall (λ _ _, (summable_geometric_of_lt_1 hwR.1 hwR.2).mul_left _) },
  { simpa only [tsum_mul_left, tsum_geometric_of_lt_1 hwR.1 hwR.2]
      using hf.norm.mul_continuous_on continuous_on_const },
  { refine eventually_of_forall (λ θ hθ, has_sum.const_smul _),
    simp only [smul_smul],
    refine has_sum.smul_const _,
    have : ∥w / (circle_map c R θ - c)∥ < 1, by simpa [abs_of_pos hR] using hwR.2,
    convert (has_sum_geometric_of_norm_lt_1 this).mul_right _,
    simp [← sub_sub, ← mul_inv₀, sub_mul, div_mul_cancel _ (circle_map_ne_center hR.ne')] }
end

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
lemma has_sum_cauchy_power_series_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
  (hf : circle_integrable f c R) (hw : abs w < R) :
  has_sum (λ n, cauchy_power_series f c R n (λ _, w))
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) :=
begin
  simp only [cauchy_power_series_apply],
  exact (has_sum_two_pi_I_cauchy_power_series_integral hf hw).const_smul
end

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
lemma sum_cauchy_power_series_eq_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
  (hf : circle_integrable f c R) (hw : abs w < R) :
  (cauchy_power_series f c R).sum w =
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) :=
(has_sum_cauchy_power_series_integral hf hw).tsum_eq

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
lemma has_fpower_series_on_cauchy_integral {f : ℂ → E} {c : ℂ} {R : ℝ≥0}
  (hf : circle_integrable f c R) (hR : 0 < R) :
  has_fpower_series_on_ball
    (λ w, (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z)
    (cauchy_power_series f c R) c R :=
{ r_le := le_radius_cauchy_power_series _ _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ y hy,
    begin
      refine has_sum_cauchy_power_series_integral hf _,
      rw [← norm_eq_abs, ← coe_nnnorm, nnreal.coe_lt_coe, ← ennreal.coe_lt_coe],
      exact mem_emetric_ball_zero_iff.1 hy
    end }

namespace circle_integral

/-- Integral $\oint_{|z-c|=R} \frac{dz}{z-w}=2πi$ whenever $|w-c|<R$. -/
lemma integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
  ∮ z in C(c, R), (z - w)⁻¹ = 2 * π * I :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw,
  suffices H : has_sum (λ n : ℕ, ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹) (2 * π * I),
  { have A : circle_integrable (λ _, (1 : ℂ)) c R, from continuous_on_const.circle_integrable',
    refine (H.unique _).symm,
    simpa only [smul_eq_mul, mul_one, add_sub_cancel'_right]
      using has_sum_two_pi_I_cauchy_power_series_integral A hw },
  have H : ∀ n : ℕ, n ≠ 0 → ∮ z in C(c, R), (z - c) ^ (-n - 1 : ℤ) = 0,
  { refine λ n hn, integral_sub_zpow_of_ne _ _ _ _, simpa },
  have : ∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹ = 2 * π * I, by simp [hR.ne'],
  refine this ▸ has_sum_single _ (λ n hn, _),
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc],
  rw [(integral_congr hR.le (λ z hz, _)).trans (H n hn), mul_zero],
  rw [← pow_succ', ← zpow_coe_nat, inv_zpow₀, ← zpow_neg₀, int.coe_nat_succ, neg_add,
    sub_eq_add_neg _ (1 : ℤ)]
end

end circle_integral
