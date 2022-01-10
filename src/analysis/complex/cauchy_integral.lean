/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.complex_lebesgue
import measure_theory.integral.divergence_theorem
import measure_theory.integral.circle_integral
import analysis.calculus.fderiv_analytic
import analysis.calculus.dslope
import analysis.complex.re_im_topology
import analysis.asymptotics.specific_asymptotics
import data.real.cardinality

/-!
# Cauchy integral formula

In this file we prove Cauchy theorem and Cauchy integral formula for integrals over circles. Most
results are formulated for a function `f : ℂ → E` that takes values in a complex Banach space with
second countable topology.

## Main statements

In the following theorems, if the name ends with `off_countable`, then the actual theorem assumes
differentiability at all but countably many points of the set mentioned below.

* `complex.integral_boundary_rect_of_has_fderiv_within_at_real_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and *real* differentiable on its interior, then
  its integral over the boundary of this rectangle is equal to the integral of
  `I • f' (x + y * I) 1 - f' (x + y * I) I` over the rectangle, where `f' z w : E` is the derivative
  of `f` at `z` in the direction `w` and `I = complex.I` is the imaginary unit.

* `complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and is *complex* differentiable on its interior,
  then its integral over the boundary of this rectangle is equal to zero.

* `complex.circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: If a
  function `f : ℂ → E` is continuous on a closed annulus `{z | r ≤ |z - c| ≤ R}` and is complex
  differentiable on its interior `{z | r < |z - c| < R}`, then the integrals of `(z - c)⁻¹ • f z`
  over the outer boundary and over the inner boundary are equal.

* `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`,
  `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable`:
  If a function `f : ℂ → E` is continuous on a punctured closed disc `{z | |z - c| ≤ R ∧ z ≠ c}`, is
  complex differentiable on the corresponding punctured open disc, and tends to `y` as `z → c`,
  `z ≠ c`, then the integral of `(z - c)⁻¹ • f z` over the circle `|z - c| = R` is equal to
  `2πiy`. In particular, if `f` is continuous on the whole closed disc and is complex differentiable
  on the corresponding open disc, then this integral is equal to `2πif(c)`.

* `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`,
  `complex.two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
  complex differentiable on the corresponding open disc, then for any `w` in the corresponding open
  disc the integral of `(z - w)⁻¹ • f z` over the boundary of the disc is equal to `2πif(w)`.
  Two versions of the lemma put the multiplier `2πi` at the different sides of the equality.

* `complex.has_fpower_series_on_ball_of_differentiable_off_countable`: If `f : ℂ → E` is continuous
  on a closed disc of positive radius and is complex differentiable on the corresponding open disc,
  then it is analytic on the corresponding open disc, and the coefficients of the power series are
  given by Cauchy integral formulas.

* `differentiable_on.has_fpower_series_on_ball`: If `f : ℂ → E` is complex differentiable on a
  closed disc of positive radius, then it is analytic on the corresponding open disc, and the
  coefficients of the power series are given by Cauchy integral formulas.

* `differentiable_on.analytic_at`, `differentiable.analytic_at`: If `f : ℂ → E` is differentiable
  on a neighborhood of a point, then it is analytic at this point. In particular, if `f : ℂ → E`
  is differentiable on the whole `ℂ`, then it is analytic at every point `z : ℂ`.

## Implementation details

The proof of the Cauchy integral formula in this file is based on a very general version of the
divergence theorem, see `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`
(a version for functions defined on `fin (n + 1) → ℝ`),
`measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`, and
`measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` (versions for
functions defined on `ℝ × ℝ`).

Usually, the divergence theorem is formulated for a $C^1$ smooth function. The theorems formulated
above deal with a function that is

* continuous on a closed box/rectangle;
* differentiable at all but countably many points of its interior;
* have divergence integrable over the closed box/rectangle.

First, we reformulate the theorem for a *real*-differentiable map `ℂ → E`, and relate the integral
of `f` over the boundary of a rectangle in `ℂ` to the integral of the derivative
$\frac{\partial f}{\partial \bar z}$ over the interior of this box. In particular, for a *complex*
differentiable function, the latter derivative is zero, hence the integral over the boundary of a
rectangle is zero. Thus we get Cauchy theorem for a rectangle in `ℂ`.

Next, we apply the this theorem to the function $F(z)=f(c+e^{z})$ on the rectangle
$[\ln r, \ln R]\times [0, 2\pi]$ to prove that
$$
  \oint_{|z-c|=r}\frac{f(z)\,dz}{z-c}=\oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}
$$
provided that `f` is continuous on the closed annulus `r ≤ |z - c| ≤ R` and is complex
differentiable on its interior `r < |z - c| < R` (possibly, at all but countably many points).

Here and below, we write $\frac{f(z)}{z-c}$ in the documentation while the actual lemmas use
`(z - c)⁻¹ • f z` because `f z` belongs to some Banach space over `ℂ` and `f z / (z - c)` is
undefined.

Taking the limit of this equality as `r` tends to `𝓝[>] 0`, we prove
$$
  \oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}=2\pi if(c)
$$
provided that `f` is continuous on the closed disc `|z - c| ≤ R` and is differentiable at all but
countably many points of its interior. This is the Cauchy integral formula for the center of a
circle. In particular, if we apply this function to `F z = (z - c) • f z`, then we get
$$
  \oint_{|z-c|=R} f(z)\,dz=0.
$$

In order to deduce the Cauchy integral formula for any point `w`, `|w - c| < R`, we consider the
slope function `g : ℂ → E` given by `g z = (z - w)⁻¹ • (f z - f w)` if `z ≠ w` and `g w = f' w`.
This function satisfies assumptions of the previous theorem, so we have
$$
  \oint_{|z-c|=R} \frac{f(z)\,dz}{z-w}=\oint_{|z-c|=R} \frac{f(w)\,dz}{z-w}=
  \left(\oint_{|z-c|=R} \frac{dz}{z-w}\right)f(w).
$$
The latter integral was computed in `circle_integral.integral_sub_inv_of_mem_ball` and is equal to
`2 * π * complex.I`.

There is one more step in the actual proof. Since we allow `f` to be non-differentiable on a
countable set `s`, we cannot immediately claim that `g` is continuous at `w` if `w ∈ s`. So, we use
the proof outlined in the previous paragraph for `w ∉ s` (see
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux`), then use continuity
of both sides of the formula and density of `sᶜ` to prove the formula for all points of the open
ball, see `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`.

Finally, we use the properties of the Cauchy integrals established elsewhere (see
`has_fpower_series_on_cauchy_integral`) and Cauchy integral formula to prove that the original
function is analytic on the open ball.

## Tags

Cauchy theorem, Cauchy integral formula
-/

open topological_space set measure_theory interval_integral metric filter function asymptotics
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u

variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corresponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_has_fderiv_at_real_off_countable (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : continuous_on f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]))
  (Hd : ∀ x ∈ (re ⁻¹' (Ioo (min z.re w.re) (max z.re w.re)) ∩
    im ⁻¹' (Ioo (min z.im w.im) (max z.im w.im))) \ s, has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ z, I • f' z 1 - f' z I) (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im])) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
    ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
begin
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equiv_real_prodₗ.symm,
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y), from λ x y, (mk_eq_add_mul_I x y).symm,
  have he₁ : e (1, 0) = 1 := rfl, have he₂ : e (0, 1) = I := rfl,
  simp only [he] at *,
  set F : (ℝ × ℝ) → E := f ∘ e,
  set F' : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] E := λ p, (f' (e p)).comp (e : (ℝ × ℝ) →L[ℝ] ℂ),
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I),
  { rintro ⟨x, y⟩, simp [F', he₁, he₂, ← sub_eq_neg_add], },
  set R : set (ℝ × ℝ) := [z.re, w.re].prod [w.im, z.im],
  set t : set (ℝ × ℝ) := e ⁻¹' s,
  rw [interval_swap z.im] at Hc Hi, rw [min_comm z.im, max_comm z.im] at Hd,
  have hR : e ⁻¹' (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [w.im, z.im]) = R := rfl,
  have htc : continuous_on F R, from Hc.comp e.continuous_on hR.ge,
  have htd : ∀ p ∈ (Ioo (min z.re w.re) (max z.re w.re)).prod
    (Ioo (min w.im z.im) (max w.im z.im)) \ t, has_fderiv_at F (F' p) p,
    from λ p hp, (Hd (e p) hp).comp p e.has_fderiv_at,
  simp_rw [← interval_integral.integral_smul, interval_integral.integral_symm w.im z.im,
    ← interval_integral.integral_neg, ← hF'],
  refine (integral2_divergence_prod_of_has_fderiv_within_at_off_countable
      (λ p, -(I • F p)) F (λ p, - (I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
      (continuous_on_const.smul htc).neg htc (λ p hp, ((htd p hp).const_smul I).neg) htd _).symm,
  rw [← volume_preserving_equiv_real_prod.symm.integrable_on_comp_preimage
    (measurable_equiv.measurable_embedding _)] at Hi,
  simpa only [hF'] using Hi.neg
end

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the integral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_continuous_on_of_has_fderiv_at_real (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
  (Hc : continuous_on f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]))
  (Hd : ∀ x ∈ (re ⁻¹' (Ioo (min z.re w.re) (max z.re w.re)) ∩
    im ⁻¹' (Ioo (min z.im w.im) (max z.im w.im))), has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ z, I • f' z 1 - f' z I) (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im])) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
    ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
integral_boundary_rect_of_has_fderiv_at_real_off_countable f f' z w ∅ countable_empty Hc
  (λ x hx, Hd x hx.1) Hi

/-- Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectangle with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_differentiable_on_real (f : ℂ → E) (z w : ℂ)
  (Hd : differentiable_on ℝ f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]))
  (Hi : integrable_on (λ z, I • fderiv ℝ f z 1 - fderiv ℝ f z I)
    (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im])) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
    ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im,
      I • fderiv ℝ f (x + y * I) 1 - fderiv ℝ f (x + y * I) I :=
integral_boundary_rect_of_has_fderiv_at_real_off_countable f (fderiv ℝ f) z w ∅ countable_empty
  Hd.continuous_on
  (λ x hx, Hd.has_fderiv_at $ by simpa only [← mem_interior_iff_mem_nhds,
    interior_preimage_re_inter_preimage_im, interval, interior_Icc] using hx.1) Hi

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
rectangle equals zero. More precisely, if `f` is continuous on a closed rectangle and is complex
differentiable at all but countably many points of the corresponding open rectangle, then its
integral over the boundary of the rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E)
  (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : continuous_on f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]))
  (Hd : ∀ x ∈ (re ⁻¹' (Ioo (min z.re w.re) (max z.re w.re)) ∩
    im ⁻¹' (Ioo (min z.im w.im) (max z.im w.im))) \ s, differentiable_at ℂ f x) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) = 0 :=
by refine (integral_boundary_rect_of_has_fderiv_at_real_off_countable f
  (λ z, (fderiv ℂ f z).restrict_scalars ℝ) z w s hs Hc
  (λ x hx, (Hd x hx).has_fderiv_at.restrict_scalars ℝ) _).trans _;
    simp [← continuous_linear_map.map_smul]

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
rectangle equals zero. More precisely, if `f` is continuous on a closed rectangle and is complex
differentiable on the corresponding open rectangle, then its integral over the boundary of the
rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on (f : ℂ → E) (z w : ℂ)
  (Hc : continuous_on f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]))
  (Hd : differentiable_on ℂ f (re ⁻¹' (Ioo (min z.re w.re) (max z.re w.re)) ∩
    im ⁻¹' (Ioo (min z.im w.im) (max z.im w.im)))) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) = 0 :=
integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty
  Hc $ λ x hx, Hd.differentiable_at $ (is_open_Ioo.re_prod_im is_open_Ioo).mem_nhds hx.1

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
rectangle equals zero. More precisely, if `f` is complex differentiable on a closed rectangle, then
its integral over the boundary of the rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_differentiable_on (f : ℂ → E) (z w : ℂ)
  (H : differentiable_on ℂ f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im])) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) = 0 :=
integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on f z w H.continuous_on $
  H.mono $
    inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

/-- If `f : ℂ → E` is continuous the closed annulus `r ≤ ∥z - c∥ ≤ R`, `0 < r ≤ R`, and is complex
differentiable at all but countably many points of its interior, then the integrals of
`f z / (z - c)` (formally, `(z - c)⁻¹ • f z`) over the circles `∥z - c∥ = r` and `∥z - c∥ = R` are
equal to each other. -/
lemma circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
  {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : countable s)
  (hc : continuous_on f (closed_ball c R \ ball c r))
  (hd : ∀ z ∈ ball c R \ closed_ball c r \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = ∮ z in C(c, r), (z - c)⁻¹ • f z :=
begin
  /- We apply the previous lemma to `λ z, f (c + exp z)` on the rectangle
  `[log r, log R] × [0, 2 * π]`. -/
  set A := closed_ball c R \ ball c r,
  obtain ⟨a, rfl⟩ : ∃ a, real.exp a = r, from ⟨real.log r, real.exp_log h0⟩,
  obtain ⟨b, rfl⟩ : ∃ b, real.exp b = R, from ⟨real.log R, real.exp_log (h0.trans_le hle)⟩,
  rw [real.exp_le_exp] at hle,
  -- Unfold definition of `circle_integral` and cancel some terms.
  suffices : ∫ θ in 0..2 * π, I • f (circle_map c (real.exp b) θ) =
    ∫ θ in 0..2 * π, I • f (circle_map c (real.exp a) θ),
    by simpa only [circle_integral, add_sub_cancel', of_real_exp, ← exp_add, smul_smul,
      ← div_eq_mul_inv, mul_div_cancel_left _ (circle_map_ne_center (real.exp_pos _).ne'),
      circle_map_sub_center, deriv_circle_map],
  set R := re ⁻¹' [a, b] ∩ im ⁻¹' [0, 2 * π],
  set g : ℂ → ℂ := (+) c ∘ exp,
  have hdg : differentiable ℂ g := differentiable_exp.const_add _,
  replace hs : countable (g ⁻¹' s) := (hs.preimage (add_right_injective c)).preimage_cexp,
  have h_maps : maps_to g R A,
  { rintro z ⟨h, -⟩, simpa [dist_eq, g, abs_exp, hle] using h.symm },
  replace hc : continuous_on (f ∘ g) R, from hc.comp hdg.continuous.continuous_on h_maps,
  replace hd : ∀ z ∈ re ⁻¹' (Ioo (min a b) (max a b)) ∩
    im ⁻¹' (Ioo (min 0 (2 * π)) (max 0 (2 * π))) \ g ⁻¹' s, differentiable_at ℂ (f ∘ g) z,
  { refine λ z hz, (hd (g z) ⟨_, hz.2⟩).comp z (hdg _),
    simpa [g, dist_eq, abs_exp, hle, and.comm] using hz.1.1 },
  simpa [g, circle_map, exp_periodic _, sub_eq_zero, ← exp_add]
    using integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩
      _ hs hc hd
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is continuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many points of the
interior of this disc, and has a limit `y` at the center of the disc, then the integral
$\oint_{∥z-c∥=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
  {c : ℂ} {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : set ℂ} (hs : countable s)
  (hc : continuous_on f (closed_ball c R \ {c}))
  (hd : ∀ z ∈ ball c R \ {c} \ s, differentiable_at ℂ f z)
  (hy : tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = (2 * π * I : ℂ) • y :=
begin
  rw [← sub_eq_zero, ← norm_le_zero_iff],
  refine le_of_forall_le_of_dense (λ ε ε0, _),
  obtain ⟨δ, δ0, hδ⟩ :
    ∃ δ > (0 : ℝ), ∀ z ∈ closed_ball c δ \ {c}, dist (f z) y < ε / (2 * π),
    from ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 real.two_pi_pos),
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩,
  have hsub : closed_ball c R \ ball c r ⊆ closed_ball c R \ {c},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_ball_self hr0),
  have hsub' : ball c R \ closed_ball c r ⊆ ball c R \ {c},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_closed_ball_self hr0.le),
  have hzne : ∀ z ∈ sphere c r, z ≠ c,
    from λ z hz, ne_of_mem_of_not_mem hz (λ h, hr0.ne' $ dist_self c ▸ eq.symm h),
  /- The integral `∮ z in C(c, r), f z / (z - c)` does not depend on `0 < r ≤ R` and tends to
  `2πIy` as `r → 0`. -/
  calc ∥(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y∥
      = ∥(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y∥ :
    begin
      congr' 2,
      { exact circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
          hr0 hrR hs (hc.mono hsub) (λ z hz, hd z ⟨hsub' hz.1, hz.2⟩) },
      { simp [hr0.ne'] }
    end
  ... = ∥∮ z in C(c, r), (z - c)⁻¹ • (f z - y)∥ :
    begin
      simp only [smul_sub],
      have hc' : continuous_on (λ z, (z - c)⁻¹) (sphere c r),
        from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hzne _ hz),
      rw circle_integral.integral_sub; refine (hc'.smul _).circle_integrable hr0.le,
      { exact hc.mono (subset_inter (sphere_subset_closed_ball.trans $
          closed_ball_subset_closed_ball hrR) hzne) },
      { exact continuous_on_const }
    end
  ... ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) :
    begin
      refine circle_integral.norm_integral_le_of_norm_le_const hr0.le (λ z hz, _),
      specialize hzne z hz,
      rw [mem_sphere, dist_eq_norm] at hz,
      rw [norm_smul, normed_field.norm_inv, hz, ← dist_eq_norm],
      refine mul_le_mul_of_nonneg_left (hδ _ ⟨_, hzne⟩).le (inv_nonneg.2 hr0.le),
      rwa [mem_closed_ball_iff_norm, hz]
    end
  ... = ε : by { field_simp [hr0.ne', real.two_pi_pos.ne'], ac_refl }
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E` is continuous
on a closed disc of radius `R` and is complex differentiable at all but countably many points of its
interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
  {f : ℂ → E} {c : ℂ} {s : set ℂ} (hs : countable s)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = (2 * π * I : ℂ) • f c :=
circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
  (hc.mono $ diff_subset _ _) (λ z hz, hd z ⟨hz.1.1, hz.2⟩)
  (hc.continuous_at $ closed_ball_mem_nhds _ h0).continuous_within_at

/-- **Cauchy theorem**: if `f : ℂ → E` is continuous on a closed ball `{z | ∥z - c∥ ≤ R}` and is
complex differentiable at all but countably many points of its interior, then the integral
$\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
lemma circle_integral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {c : ℂ} {s : set ℂ} (hs : countable s) (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), f z = 0 :=
begin
  rcases h0.eq_or_lt with rfl|h0, { apply circle_integral.integral_radius_zero },
  calc ∮ z in C(c, R), f z = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :
    begin
      refine circle_integral.integral_congr h0.le (λ z hz, (inv_smul_smul₀ (λ h₀, _) _).symm),
      rw [mem_sphere, dist_eq, h₀, abs_zero] at hz,
      exact h0.ne hz
    end
  ... = (2 * ↑π * I : ℂ) • (c - c) • f c :
    circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
      ((continuous_on_id.sub continuous_on_const).smul hc)
      (λ z hz, (differentiable_at_id.sub_const _).smul (hd z hz))
  ... = 0 : by rw [sub_self, zero_smul, smul_zero]
end

/-- An auxiliary lemma for
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`. This lemma assumes
`w ∉ s` while the main lemma drops this assumption. -/
lemma circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ}
  {f : ℂ → E} {s : set ℂ} (hs : countable s) (hw : w ∈ ball c R \ s)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw.1,
  set F : ℂ → E := dslope f w,
  have hws : countable (insert w s) := hs.insert _,
  have hnhds : closed_ball c R ∈ 𝓝 w, from closed_ball_mem_nhds_of_mem hw.1,
  have hcF : continuous_on F (closed_ball c R),
    from (continuous_on_dslope $ closed_ball_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩,
  have hdF : ∀ z ∈ ball (c : ℂ) R \ (insert w s), differentiable_at ℂ F z,
    from λ z hz, (differentiable_at_dslope_of_ne
      (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (diff_subset_diff_right (subset_insert _ _) hz)),
  have HI := circle_integral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF,
  have hne : ∀ z ∈ sphere c R, z ≠ w, from λ z hz, ne_of_mem_of_not_mem hz (ne_of_lt hw.1),
  have hFeq : eq_on F (λ z, (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R),
  { intros z hz,
    calc F z = (z - w)⁻¹ • (f z - f w) : update_noteq (hne z hz) _ _
    ... = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w : smul_sub _ _ _ },
  have hc' : continuous_on (λ z, (z - w)⁻¹) (sphere c R),
    from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hne z hz),
  rw [← circle_integral.integral_sub_inv_of_mem_ball hw.1, ← circle_integral.integral_smul_const,
    ← sub_eq_zero, ← circle_integral.integral_sub, ← circle_integral.integral_congr hR.le hFeq, HI],
  exacts [(hc'.smul (hc.mono sphere_subset_closed_ball)).circle_integrable hR.le,
    (hc'.smul continuous_on_const).circle_integrable hR.le]
end

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
lemma two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : set ℂ} (hs : countable s) (hw : w ∈ ball c R)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z = f w :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw,
  suffices : w ∈ closure (ball c R \ s),
  { lift R to ℝ≥0 using hR.le,
    have A : continuous_at (λ w, (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w,
    { have := has_fpower_series_on_cauchy_integral
      ((hc.mono sphere_subset_closed_ball).circle_integrable R.coe_nonneg) hR,
      refine this.continuous_on.continuous_at (emetric.is_open_ball.mem_nhds _),
      rwa metric.emetric_ball_nnreal },
    have B : continuous_at f w, from hc.continuous_at (closed_ball_mem_nhds_of_mem hw),
    refine tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono _),
    intros z hz,
    rw [circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd,
      inv_smul_smul₀],
    simp [real.pi_ne_zero, I_ne_zero] },
  refine mem_closure_iff_nhds.2 (λ t ht, _),
  -- TODO: generalize to any vector space over `ℝ`
  set g : ℝ → ℂ := λ x, w + x,
  have : tendsto g (𝓝 0) (𝓝 w),
    from (continuous_const.add continuous_of_real).tendsto' 0 w (add_zero _),
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this $ inter_mem ht $ is_open_ball.mem_nhds hw)
    with ⟨l, u, hlu₀, hlu_sub⟩,
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).nonempty,
  { refine nonempty_diff.2 (λ hsub, _),
    have : countable (Ioo l u),
      from (hs.preimage ((add_right_injective w).comp of_real_injective)).mono hsub,
    rw [← cardinal.mk_set_le_omega, cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this,
    exact this.not_lt cardinal.omega_lt_continuum },
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩
end

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
lemma circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : set ℂ} (hs : countable s) (hw : w ∈ ball c R)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
by { rw [← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  hs hw hc hd, smul_inv_smul₀], simp [real.pi_ne_zero, I_ne_zero] }

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable on its interior, then for any `w` in this interior we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
lemma circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on
  {R : ℝ} {c w : ℂ} {f : ℂ → E} (hw : w ∈ ball c R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R)) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
circle_integral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw hc $ λ z hz,
  hd.differentiable_at (is_open_ball.mem_nhds hz.1)

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a closed disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
lemma circle_integral_sub_inv_smul_of_differentiable_on
  {R : ℝ} {c w : ℂ} {f : ℂ → E} (hw : w ∈ ball c R) (hd : differentiable_on ℂ f (closed_ball c R)) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on hw hd.continuous_on $
  hd.mono $ ball_subset_closed_ball

/-- **Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
lemma circle_integral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : set ℂ}
  (hs : countable s) (hw : w ∈ ball c R) {f : ℂ → ℂ} (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), f z / (z - w) = 2 * π * I * f w :=
by simpa only [smul_eq_mul, div_eq_inv_mul]
  using circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is differentiable at all
but countably many points of the corresponding open ball, then it is analytic on the open ball with
coefficients of the power series given by Cauchy integral formulas. -/
lemma has_fpower_series_on_ball_of_differentiable_off_countable {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  {s : set ℂ} (hs : countable s) (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
{ r_le := le_radius_cauchy_power_series _ _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ w hw,
    begin
      have hw' : c + w ∈ ball c R,
        by simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_emetric_ball_zero_iff,
          nnreal.coe_lt_coe, ennreal.coe_lt_coe] using hw,
      rw ← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs
        hw' hc hd,
      exact (has_fpower_series_on_cauchy_integral
        ((hc.mono sphere_subset_closed_ball).circle_integrable R.2) hR).has_sum hw
    end }

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is complex differentiable
on its interior, then it is analytic on the open ball with coefficients of the power series given by
Cauchy integral formulas. -/
lemma has_fpower_series_on_ball_of_continuous_on_of_differentiable_on {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R)) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
has_fpower_series_on_ball_of_differentiable_off_countable countable_empty hc
  (λ z hz, hd.differentiable_at $ is_open_ball.mem_nhds hz.1) hR

/-- If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, then it is
analytic on the corresponding open disc, and the coefficients of the power series are given by
Cauchy integral formulas. See also
`complex.has_fpower_series_on_ball_of_differentiable_off_countable` for a version of this lemma with
weaker assumptions. -/
protected lemma _root_.differentiable_on.has_fpower_series_on_ball {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball c R)) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
has_fpower_series_on_ball_of_continuous_on_of_differentiable_on hd.continuous_on
  (hd.mono ball_subset_closed_ball) hR

/-- **Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiable in a punctured
neighborhood of a point and is continuous at a point, then it is analytic at this point. -/
lemma analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z) (hc : continuous_at f c) :
  analytic_at ℂ f c :=
begin
  rcases (nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 hd with ⟨R, hR0, hRs⟩,
  lift R to ℝ≥0 using hR0.le,
  replace hc : continuous_on f (closed_ball c R),
  { refine λ z hz, continuous_at.continuous_within_at _,
    rcases eq_or_ne z c with rfl | hne,
    exacts [hc, (hRs ⟨hz, hne⟩).continuous_at] },
  exact (has_fpower_series_on_ball_of_differentiable_off_countable (countable_singleton c) hc
    (λ z hz, hRs (diff_subset_diff_left ball_subset_closed_ball hz)) hR0).analytic_at 
end

/-- If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`). -/
protected lemma _root_.differentiable_on.analytic_at {s : set ℂ} {f : ℂ → E} {z : ℂ}
  (hd : differentiable_on ℂ f s) (hz : s ∈ 𝓝 z) : analytic_at ℂ f z :=
begin
  rcases nhds_basis_closed_ball.mem_iff.1 hz with ⟨R, hR0, hRs⟩,
  lift R to ℝ≥0 using hR0.le,
  exact ((hd.mono hRs).has_fpower_series_on_ball hR0).analytic_at
end

/-- A complex differentiable function `f : ℂ → E` is analytic at every point. -/
protected lemma _root_.differentiable.analytic_at {f : ℂ → E} (hf : differentiable ℂ f) (z : ℂ) :
  analytic_at ℂ f z :=
hf.differentiable_on.analytic_at univ_mem

lemma differentiable_on_compl_singleton_and_continuous_at_iff {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hs : s ∈ 𝓝 c) : differentiable_on ℂ f (s \ {c}) ∧ continuous_at f c ↔ differentiable_on ℂ f s :=
begin
  refine ⟨_, λ hd, ⟨hd.mono (diff_subset _ _), (hd.differentiable_at hs).continuous_at⟩⟩,
  rintro ⟨hd, hc⟩ x hx,
  rcases eq_or_ne x c with rfl | hne,
  { refine (analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at _ hc)
      .differentiable_at.differentiable_within_at,
    refine eventually_nhds_within_iff.2 ((eventually_mem_nhds.2 hs).mono $ λ z hz hzx, _),
    exact hd.differentiable_at (inter_mem hz (is_open_ne.mem_nhds hzx)) },
  { simpa only [differentiable_within_at, has_fderiv_within_at, hne.nhds_within_diff_singleton]
      using hd x ⟨hx, hne⟩ }
end

lemma differentiable_on_dslope {f : ℂ → E} {s : set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c) :
  differentiable_on ℂ (dslope f c) s ↔ differentiable_on ℂ f s :=
⟨λ h, h.of_dslope, λ h, (differentiable_on_compl_singleton_and_continuous_at_iff hc).mp $
  ⟨iff.mpr (differentiable_on_dslope_of_nmem $ λ h, h.2 rfl) (h.mono $ diff_subset _ _),
    continuous_at_dslope_same.2 $ h.differentiable_at hc⟩⟩

lemma differentiable_on_update_lim_of_is_o {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝 c) (hd : differentiable_on ℂ f (s \ {c}))
  (ho : is_o (λ z, f z - f c) (λ z, (z - c)⁻¹) (𝓝[≠] c)) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) s :=
begin
  set F : ℂ → E := λ z, (z - c) • f z with hF,
  suffices : differentiable_on ℂ F (s \ {c}) ∧ continuous_at F c,
  { rw [differentiable_on_compl_singleton_and_continuous_at_iff hc, ← differentiable_on_dslope hc,
      dslope_sub_smul] at this; try { apply_instance },
    have hc : tendsto f (𝓝[≠] c) (𝓝 (deriv F c)),
      from continuous_at_update_same.mp (this.continuous_on.continuous_at hc),
    rwa hc.lim_eq },
  refine ⟨(differentiable_on_id.sub_const _).smul hd, _⟩,
  rw ← continuous_within_at_compl_self,
  have H := ho.tendsto_inv_smul_nhds_zero,
  have H' : tendsto (λ z, (z - c) • f c) (𝓝[≠] c) (𝓝 (F c)),
    from (continuous_within_at_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds,
  simpa [← smul_add, continuous_within_at] using H.add H'
end

lemma differentiable_on_update_lim_insert_of_is_o {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝[≠] c) (hd : differentiable_on ℂ f s)
  (ho : is_o (λ z, f z - f c) (λ z, (z - c)⁻¹) (𝓝[≠] c)) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) (insert c s) :=
differentiable_on_update_lim_of_is_o (insert_mem_nhds_iff.2 hc)
  (hd.mono $ λ z hz, hz.1.resolve_left hz.2) ho

lemma differentiable_on_update_lim_of_bdd_above {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝 c) (hd : differentiable_on ℂ f (s \ {c}))
  (hb : bdd_above (norm ∘ f '' (s \ {c}))) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) s :=
differentiable_on_update_lim_of_is_o hc hd $ is_bounded_under.is_o_sub_self_inv $
  let ⟨C, hC⟩ := hb in ⟨C + ∥f c∥, eventually_map.2 $ mem_nhds_within_iff_exists_mem_nhds_inter.2
    ⟨s, hc, λ z hz, norm_sub_le_of_le (hC $ mem_image_of_mem _ hz) le_rfl⟩⟩

lemma tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z)
  (ho : is_o (λ z, f z - f c) (λ z, (z - c)⁻¹) (𝓝[≠] c)) :
  tendsto f (𝓝[≠] c) (𝓝 $ lim (𝓝[≠] c) f) :=
begin
  rw eventually_nhds_within_iff at hd,
  have : differentiable_on ℂ f ({z | z ≠ c → differentiable_at ℂ f z} \ {c}),
    from λ z hz, (hz.1 hz.2).differentiable_within_at,
  have H := differentiable_on_update_lim_of_is_o hd this ho,
  exact continuous_at_update_same.1 (H.differentiable_at hd).continuous_at
end

lemma tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under {f : ℂ → E}
  {c : ℂ} (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z)
  (hb : is_bounded_under (≤) (𝓝[≠] c) (λ z, ∥f z - f c∥)) :
  tendsto f (𝓝[≠] c) (𝓝 $ lim (𝓝[≠] c) f) :=
tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o hd hb.is_o_sub_self_inv

/-- If `f` is complex differentiable on a closed disc with center `c` and radius `R > 0`, then
`f' c` can be represented as an integral over the corresponding circle.

TODO: add a version for `w ∈ metric.ball c R`.

TODO: add a version for higher derivatives. -/
lemma deriv_eq_smul_circle_integral {R : ℝ} {c : ℂ} {f : ℂ → E} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R)) :
  deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z :=
begin
  lift R to ℝ≥0 using hR.le,
  refine (has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
    hc hd hR).has_fpower_series_at.deriv.trans _,
  simp only [cauchy_power_series_apply, one_div, zpow_neg₀, pow_one, smul_smul,
    zpow_two, mul_inv₀]
end

/-- If `f` is continuous on a closed disc of radius `R`, is complex differentiable on its interior,
and its values on the boundary circle of this disc are bounded from above by `C`, then the norm of
its derivative at the center is at most `C / R`. -/
lemma norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → E} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R))
  (hC : ∀ z ∈ sphere c R, ∥f z∥ ≤ C) :
  ∥deriv f c∥ ≤ C / R :=
have ∀ z ∈ sphere c R, ∥(z - c) ^ (-2 : ℤ) • f z∥ ≤ C / (R * R),
  from λ z (hz : abs (z - c) = R), by simpa [norm_smul, hz, zpow_two, ← div_eq_inv_mul]
    using (div_le_div_right (mul_pos hR hR)).2 (hC z hz),
calc ∥deriv f c∥ = ∥(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z∥ :
  congr_arg norm (deriv_eq_smul_circle_integral hR hc hd)
... ≤ R * (C / (R * R)) :
  circle_integral.norm_two_pi_I_inv_smul_integral_le_of_norm_le_const hR.le this
... = C / R : by rw [mul_div_comm, div_self_mul_self', div_eq_mul_inv]

/-- A complex differentiable bounded function is a constant. -/
lemma apply_eq_apply_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) (z w : ℂ) : f z = f w :=
begin
  suffices : ∀ c, deriv f c = 0, from is_const_of_deriv_eq_zero hf this z w,
  clear z w, intro c,
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ∥f z∥ ≤ C,
  { rcases bounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩,
    exact ⟨max C 1, lt_max_iff.2 (or.inr zero_lt_one),
      λ z, (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩ },
  refine norm_le_zero_iff.1 (le_of_forall_le_of_dense $ λ ε ε₀, _),
  calc ∥deriv f c∥ ≤ C / (C / ε) :
    norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.continuous.continuous_on
      hf.differentiable_on (λ z _, hC z)
  ... = ε : div_div_cancel' C₀.lt.ne'
end

/-- A complex differentiable bounded function is a constant. -/
lemma exists_const_forall_eq_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, ∀ z, f z = c :=
⟨f 0, λ z, apply_eq_apply_of_differentiable_of_bounded hf hb _ _⟩

/-- A complex differentiable bounded function is a constant. -/
lemma exists_eq_const_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, f = const ℂ c :=
(exists_const_forall_eq_of_differentiable_of_bounded hf hb).imp $ λ c, funext

lemma norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset {f : ℂ → E} {s : set ℂ}
  {z w : ℂ} (hd : differentiable_on ℂ f s) (hz : is_max_on (norm ∘ f) s z)
  (hsub : closed_ball z (dist w z) ⊆ s) :
  ∥f w∥ = ∥f z∥ :=
begin
  set r := dist w z,
  have hw_mem : w ∈ closed_ball z r, from mem_closed_ball.2 le_rfl,
  refine (is_max_on_iff.1 hz _ (hsub hw_mem)).antisymm (not_lt.1 _),
  rintro hw_lt : ∥f w∥ < ∥f z∥,
  have hr : 0 < r, from dist_pos.2 (λ h, hw_lt.ne $ h ▸ rfl),
  have hsub' : sphere z r ⊆ s, from sphere_subset_closed_ball.trans hsub,
  have hne : ∀ ζ ∈ sphere z r, ζ ≠ z,
    from λ ζ hζ, ne_of_mem_of_not_mem hζ (ne_of_lt $ (dist_self z).symm ▸ hr),
  have hcont : continuous_on (λ ζ, (ζ - z)⁻¹ • f ζ) (sphere z r),
    from ((continuous_on_id.sub continuous_on_const).inv₀ $
      λ ζ hζ, sub_ne_zero.2 (hne ζ hζ)).smul (hd.continuous_on.mono hsub'),
  have hle : ∀ ζ ∈ sphere z r, ∥(ζ - z)⁻¹ • f ζ∥ ≤ ∥f z∥ / r,
  { rintros ζ (hζ : abs (ζ - z) = r),
    simpa [norm_smul, hζ, ← div_eq_inv_mul] using (div_le_div_right hr).2 (hz (hsub' hζ)) },
  have hlt : ∥(w - z)⁻¹ • f w∥ < ∥f z∥ / r,
    by simpa [norm_smul, ← div_eq_inv_mul] using (div_lt_div_right hr).2 hw_lt,
  have : ∥∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ∥ < 2 * π * r * (∥f z∥ / r),
    from circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr hcont hle ⟨w, rfl, hlt⟩,
  refine this.ne _,
  rw circle_integral_sub_inv_smul_of_differentiable_on (mem_ball_self hr) (hd.mono hsub),
  field_simp [norm_smul, hr.ne', abs_of_pos real.pi_pos],
  ac_refl
end

lemma norm_eventually_eq_of_eventually_differentiable_at_of_is_local_max {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ∥f y∥ = ∥f c∥ :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, λ w hw,
    norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset
      (λ z hz, (hr hz).1.differentiable_within_at) (λ z hz, (hr hz).2)
      (closed_ball_subset_closed_ball hw)⟩
end

lemma is_open_set_of_mem_nhds_and_is_max_on_norm {f : ℂ → E} {s : set ℂ}
  (hd : differentiable_on ℂ f s) :
  is_open {z | s ∈ 𝓝 z ∧ is_max_on (norm ∘ f) s z} :=
begin
  refine is_open_iff_mem_nhds.2 (λ z hz, (eventually_eventually_nhds.2 hz.1).and _),
  replace hd : ∀ᶠ w in 𝓝 z, differentiable_at ℂ f w, from hd.eventually_differentiable_at hz.1,
  exact (norm_eventually_eq_of_eventually_differentiable_at_of_is_local_max hd $
    (hz.2.is_local_max hz.1)).mono (λ x hx y hy, le_trans (hz.2 hy) hx.ge)
end

/-- **Maximum modulus principle**: if `f : ℂ → E` is complex differentiable on a nonempty compact
set `s`, then there exists a point `z ∈ frontier s` such that `λ z, ∥f z∥` takes it maximum value on
`s` at `z`. -/
lemma exists_mem_frontier_is_max_on_norm {f : ℂ → E} {s : set ℂ} (hs : is_compact s)
  (hne : s.nonempty) (hd : differentiable_on ℂ f s) :
  ∃ z ∈ frontier s, is_max_on (norm ∘ f) s z :=
begin
  rcases hs.exists_forall_ge hne hd.continuous_on.norm with ⟨w, hws, hle⟩,
  rcases exists_mem_frontier_inf_dist_compl_eq_dist hws hs.ne_univ with ⟨z, hzs, hzw⟩,
  refine ⟨z, hzs, λ x hx, (hle x hx).trans_eq _⟩,
  refine (norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset hd hle _).symm,
  calc closed_ball w (dist z w) ⊆ closed_ball w (inf_dist w sᶜ) :
    closed_ball_subset_closed_ball (by rw [hzw, dist_comm])
  ... ⊆ closure s : closed_ball_inf_dist_compl_subset_closure hws hs.ne_univ
  ... = s : hs.is_closed.closure_eq
end

/-- **Maximum modulus principle**: if `f : ℂ → E` is complex differentiable on a compact set `s` and
`∥f z∥ ≤ C` for any `z ∈ frontier s`, then the same is true for any `z ∈ s`. -/
lemma norm_le_of_forall_mem_frontier_norm_le {f : ℂ → E} {s : set ℂ} (hs : is_compact s)
  (hd : differentiable_on ℂ f s) {C : ℝ} (hC : ∀ z ∈ frontier s, ∥f z∥ ≤ C) {z : ℂ} (hz : z ∈ s) :
  ∥f z∥ ≤ C :=
let ⟨w, hws, hw⟩ := exists_mem_frontier_is_max_on_norm hs ⟨z, hz⟩ hd in le_trans (hw hz) (hC w hws)

end complex
