/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.complex_lebesgue
import measure_theory.integral.divergence_theorem
import measure_theory.integral.circle_integral
import analysis.calculus.fderiv_analytic

/-!
# Cauchy integral formula

In this file we prove Cauchy theorem and Cauchy integral formula.
-/

open topological_space set measure_theory interval_integral metric filter function
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u

variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex

/-- Suppose that a function `f : ℂ → E` be is real differentiable on a rectangle with vertices
`z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle.

Moreover, the same is true if `f` is only differentiable at points outside of a countable set `s`
and is continuous at the points of this set. -/
lemma integral_boundary_rect_of_has_fderiv_within_at_real_off_countable (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
  (Hd : ∀ x ∈ (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) \ s, has_fderiv_within_at f (f' x)
    (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
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
  rw [interval_swap z.im] at Hc Hd Hi,
  have hR : e ⁻¹' (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [w.im, z.im]) = R := rfl,
  have htc : ∀ p ∈ t, continuous_within_at F R p,
    from λ p hp, (Hc (e p) hp).comp e.continuous_within_at hR.ge,
  have htd : ∀ p ∈ R \ t, has_fderiv_within_at F (F' p) R p,
    from λ p hp, (Hd (e p) hp).comp p e.has_fderiv_within_at hR.ge,
  simp_rw [← interval_integral.integral_smul, interval_integral.integral_symm w.im z.im,
    ← interval_integral.integral_neg, ← hF'],
  refine (integral2_divergence_prod_of_has_fderiv_within_at_off_countable
      (λ p, -(I • F p)) F (λ p, - (I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
      (λ p hp, (continuous_within_at_const.smul (htc p hp)).neg) htc
      (λ p hp, ((htd p hp).const_smul I).neg) htd _).symm,
  rw [← volume_preserving_equiv_real_prod.symm.integrable_on_comp_preimage
    (measurable_equiv.measurable_embedding _)] at Hi,
  simpa only [hF'] using Hi.neg
end

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
rectangle equals zero.

Moreover, the same is true if `f` is only differentiable at points outside of a countable set `s`
and is continuous at the points of this set. -/
lemma integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E)
  (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
  (Hd : ∀ x ∈ (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) \ s, differentiable_within_at ℂ f
    (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) = 0 :=
by refine (integral_boundary_rect_of_has_fderiv_within_at_real_off_countable f
  (λ z, (fderiv_within ℂ f _ z).restrict_scalars ℝ) z w s hs Hc
  (λ x hx, (Hd x hx).has_fderiv_within_at.restrict_scalars ℝ) _).trans _;
    simp [← continuous_linear_map.map_smul]

/-- If `f : ℂ → E` is complex differentiable on the closed annulus `r ≤ ∥z - z₀∥ ≤ R`, `0 < r ≤ R`,
then the integrals of `f z / (z - z₀)` (formally, `(z - z₀)⁻¹ • f z`) over the circles
`∥z - z₀∥ = r` and `∥z - z₀∥ = R` are equal to each other.

Moreover, the same is true if `f` is differentiable at points of the annulus outside of a countable
set `s` and is continuous at points of this set.  -/
lemma circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
  {z₀ : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball z₀ R \ ball z₀ r) z)
  (hd : ∀ z ∈ (closed_ball z₀ R \ ball z₀ r) \ s,
    differentiable_within_at ℂ f (closed_ball z₀ R \ ball z₀ r) z) :
  ∮ z in C(z₀, R), (z - z₀)⁻¹ • f z = ∮ z in C(z₀, r), (z - z₀)⁻¹ • f z :=
begin
  set A := closed_ball z₀ R \ ball z₀ r,
  obtain ⟨a, rfl⟩ : ∃ a, real.exp a = r, from ⟨real.log r, real.exp_log h0⟩,
  obtain ⟨b, rfl⟩ : ∃ b, real.exp b = R, from ⟨real.log R, real.exp_log (h0.trans_le hle)⟩,
  rw [real.exp_le_exp] at hle,
  simp only [circle_integral, add_sub_cancel', of_real_exp, ← exp_add, smul_smul,
    ← div_eq_mul_inv, mul_div_cancel_left _ (exp_ne_zero _)],
  set R := re ⁻¹' [a, b] ∩ im ⁻¹' [0, 2 * π],
  set g : ℂ → ℂ := (+) z₀ ∘ exp,
  have hdg : ∀ {z t}, differentiable_within_at ℂ g t z :=
    λ z t, differentiable_at_exp.differentiable_within_at.const_add _,
  replace hs : countable (g ⁻¹' s) := (hs.preimage (add_right_injective z₀)).preimage_cexp,
  have h_maps : maps_to g R A,
  { rintro z ⟨h, -⟩, simpa [dist_eq, g, abs_exp, hle] using h.symm },
  replace hc : ∀ z ∈ g ⁻¹' s, continuous_within_at (f ∘ g) R z,
    from λ z hz, (hc (g z) hz).comp hdg.continuous_within_at h_maps,
  replace hd : ∀ z ∈ R \ g ⁻¹' s, differentiable_within_at ℂ (f ∘ g) R z,
  { intros z hz,
    exact (hd (g z) ⟨h_maps hz.1, hz.2⟩).comp z hdg h_maps },
  simp only [circle_map_sub_center, deriv_circle_map,
    mul_div_cancel_left _ (circle_map_ne_center (real.exp_ne_zero _))],
  simpa [g, circle_map, exp_periodic _, sub_eq_zero, ← exp_add]
    using integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩
      _ hs hc hd
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is differentiable on a
punctured closed disc of radius `R` and has a limit `y` at the center of the disc, then the integral
$\int_{|z|=R} f(z)\,d(\arg z)=-i\int_{|z|=R}\frac{f(z)\,dz}{z}$ is equal to $2πy`. Moreover, the
same is true if at the points of some countable set, `f` is only continuous, not differentiable. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
  {z₀ : ℂ} {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball z₀ R \ {z₀}) z)
  (hd : ∀ z ∈ closed_ball z₀ R \ {z₀} \ s,
    differentiable_within_at ℂ f (closed_ball z₀ R \ {z₀}) z)
  (hy : tendsto f (𝓝[{z₀}ᶜ] z₀) (𝓝 y)) :
  ∮ z in C(z₀, R), (z - z₀)⁻¹ • f z = (2 * π * I : ℂ) • y :=
begin
  rw [← sub_eq_zero, ← norm_le_zero_iff],
  refine le_of_forall_le_of_dense (λ ε ε0, _),
  obtain ⟨δ, δ0, hδ⟩ :
    ∃ δ > (0 : ℝ), ∀ z ∈ closed_ball z₀ δ \ {z₀}, dist (f z) y < ε / (2 * π),
    from ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 real.two_pi_pos),
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩,
  have hsub : closed_ball z₀ R \ ball z₀ r ⊆ closed_ball z₀ R \ {z₀},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_ball_self hr0),
  have hzne : ∀ z ∈ sphere z₀ r, z ≠ z₀,
  { rintro z hz rfl,
    apply hr0.ne,
    rwa [mem_sphere, dist_self] at hz },
  calc ∥(∮ z in C(z₀, R), (z - z₀)⁻¹ • f z) - (2 * ↑π * I) • y∥
      = ∥(∮ z in C(z₀, r), (z - z₀)⁻¹ • f z) - ∮ z in C(z₀, r), (z - z₀)⁻¹ • y∥ :
    begin
      congr' 2,
      { refine circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
          hr0 hrR hs _ _,
        exacts [λ z hz, (hc z hz).mono hsub, λ z hz, (hd z ⟨hsub hz.1, hz.2⟩).mono hsub] },
      { simp [hr0.ne'] }
    end
  ... = ∥∮ z in C(z₀, r), (z - z₀)⁻¹ • (f z - y)∥ :
    begin
      simp only [smul_sub],
      have hc' : continuous_on (λ z, (z - z₀)⁻¹) (sphere z₀ r),
        from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hzne _ hz),
      rw circle_integral.integral_sub; refine (hc'.smul _).circle_integrable hr0.le,
      { have H : sphere z₀ r ⊆ closed_ball z₀ R \ {z₀},
        { refine λ z hz, ⟨_, hzne z hz⟩,
          rw [mem_sphere, dist_eq_norm] at hz,
          rwa [mem_closed_ball_iff_norm, hz] },
        intros z hz,
        by_cases hzs : z ∈ s,
        exacts [(hc z hzs).mono H, (hd z ⟨H hz, hzs⟩).continuous_within_at.mono H] },
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

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is differentiable on a
closed disc of radius `R`, then the integral
$\int_{|z|=R} f(z)\,d(\arg z)=-i\int_{|z|=R}\frac{f(z)\,dz}{z}$ is equal to $2πy`. Moreover, the
same is true if at the points of some countable set, `f` is only continuous, not differentiable. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
  {f : ℂ → E} {z₀ : ℂ} {s : set ℂ} (hs : countable s)
  (hc : ∀ x ∈ s, continuous_within_at f (closed_ball z₀ R) x)
  (hd : ∀ z ∈ closed_ball z₀ R \ s, differentiable_within_at ℂ f (closed_ball z₀ R) z) :
  ∮ z in C(z₀, R), (z - z₀)⁻¹ • f z = (2 * π * I : ℂ) • f z₀ :=
begin
  refine circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (λ z hz, (hc z hz).mono $ diff_subset _ _)
    (λ z hz, (hd z ⟨hz.1.1, hz.2⟩).mono $ diff_subset _ _) _,
  suffices : continuous_within_at f (closed_ball z₀ R) z₀,
    from (this.continuous_at (closed_ball_mem_nhds _ h0)).continuous_within_at,
  by_cases h : (z₀ : ℂ) ∈ s,
  exacts [hc _ h, (hd _ ⟨mem_closed_ball_self h0.le, h⟩).continuous_within_at]
end

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
disc equals zero. Moreover, the same is true if at the points of some countable set, `f` is only
continuous. -/
lemma circle_integral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {z₀ : ℂ}
  {s : set ℂ} (hs : countable s) (hc : ∀ x ∈ s, continuous_within_at f (closed_ball z₀ R) x)
  (hd : ∀ z ∈ closed_ball z₀ R \ s, differentiable_within_at ℂ f (closed_ball z₀ R) z) :
  ∮ z in C(z₀, R), f z = 0 :=
begin
  rcases h0.eq_or_lt with rfl|h0, { apply circle_integral.integral_radius_zero },
  calc ∮ z in C(z₀, R), f z = ∮ z in C(z₀, R), (z - z₀)⁻¹ • (z - z₀) • f z :
    begin
      refine circle_integral.integral_congr h0.le (λ z hz, (inv_smul_smul₀ (λ h₀, _) _).symm),
      rw [mem_sphere, dist_eq, h₀, abs_zero] at hz,
      exact h0.ne hz
    end
  ... = (2 * ↑π * I : ℂ) • (z₀ - z₀) • f z₀ :
    circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
      (λ z hz, (continuous_within_at_id.sub continuous_within_at_const).smul (hc z hz))
      (λ z hz, (differentiable_within_at_id.sub_const _).smul (hd z hz))
  ... = 0 : by rw [sub_self, zero_smul, smul_zero]
end
    
lemma circle_integral_sub_inv_smul_of_differentiable_on {R : ℝ} {c w : ℂ} (hw : w ∈ ball c R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball c R)) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw,
  set F : ℂ → E := update (λ z, (z - w)⁻¹ • (f z - f w)) w (deriv f w),
  set s : set ℂ := {w},
  have hnhds : closed_ball c R ∈ 𝓝 w, from closed_ball_mem_nhds_of_mem hw,
  have hc : ∀ z ∈ s, continuous_within_at F (closed_ball c R) z,
  { rintro z (rfl|_),
    have := has_deriv_at_iff_tendsto_slope.1 (hd.has_deriv_at hnhds),
    rw continuous_within_at_update_same,
    exact this.mono_left (nhds_within_mono _ (inter_subset_right _ _)) },
  have hdF : ∀ z ∈ closed_ball (c : ℂ) R \ s, differentiable_within_at ℂ F (closed_ball c R) z,
  { rintro z ⟨hzR, hzw : z ≠ w⟩,
    refine (((differentiable_within_at_id.sub_const w).inv $ sub_ne_zero.2 hzw).smul
      ((hd z hzR).sub_const (f w))).congr_of_eventually_eq _ _,
    { filter_upwards [mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds hzw)],
      exact λ x hx, update_noteq hx _ _ },
    { exact update_noteq hzw _ _ } },
  have HI := circle_integral_eq_zero_of_differentiable_on_off_countable hR.le
    (countable_singleton w) hc hdF,
  have hne : ∀ z ∈ sphere c R, z ≠ w, from λ z hz, ne_of_mem_of_not_mem hz (ne_of_lt hw),
  have hFeq : eq_on F (λ z, (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R),
  { intros z hz,
    calc F z = (z - w)⁻¹ • (f z - f w) : update_noteq (hne z hz) _ _
    ... = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w : smul_sub _ _ _ },
  have hc : continuous_on (λ z, (z - w)⁻¹) (sphere c R),
    from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hne z hz),
  rw [← circle_integral.integral_sub_inv_of_mem_ball hw, ← circle_integral.integral_smul_const,
    ← sub_eq_zero, ← circle_integral.integral_sub, ← circle_integral.integral_congr hR.le hFeq, HI],
  exacts [(hc.smul (hd.continuous_on.mono sphere_subset_closed_ball)).circle_integrable hR.le,
    (hc.smul continuous_on_const).circle_integrable hR.le]
end

lemma circle_integral_div_sub_of_differentiable_on {R : ℝ} {c w : ℂ} (hw : w ∈ ball c R)
  {f : ℂ → ℂ} (hd : differentiable_on ℂ f (closed_ball c R)) :
  ∮ z in C(c, R), f z / (z - w) = 2 * π * I * f w :=
by simpa only [smul_eq_mul, div_eq_inv_mul]
  using circle_integral_sub_inv_smul_of_differentiable_on hw hd

protected lemma _root_.differentiable_on.has_fpower_series_on_ball {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball c R)) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
{ r_le := le_radius_cauchy_power_series _ _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ w hw,
    begin
      have hw' : c + w ∈ ball c R,
        by simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_emetric_ball_zero_iff,
          nnreal.coe_lt_coe, ennreal.coe_lt_coe] using hw,
      convert (has_fpower_series_on_cauchy_integral _ hR).has_sum hw,
      { rw [circle_integral_sub_inv_smul_of_differentiable_on hw' hd, inv_smul_smul₀],
        simp [real.pi_ne_zero, I_ne_zero] },
      { exact (hd.mono sphere_subset_closed_ball).continuous_on.circle_integrable R.2 }
    end }

protected lemma _root_.differentiable_on.analytic_at {s : set ℂ} {f : ℂ → E} {z : ℂ}
  (hd : differentiable_on ℂ f s) (hz : s ∈ 𝓝 z) : analytic_at ℂ f z :=
begin
  rcases nhds_basis_closed_ball.mem_iff.1 hz with ⟨R, hR0, hRs⟩,
  lift R to ℝ≥0 using hR0.le,
  exact ((hd.mono hRs).has_fpower_series_on_ball hR0).analytic_at
end

protected lemma differentiable.analytic_at {f : ℂ → E} (hf : differentiable ℂ f) (z : ℂ) :
  analytic_at ℂ f z :=
hf.differentiable_on.analytic_at univ_mem

/-- If `f` is complex differentiable on a closed disc with center `c` and radius `R > 0`, then
`f' c` can be represented as an integral over the corresponding circle.

TODO: add a version for `w ∈ metric.ball c R`.

TODO: add a version for higher derivatives. -/
lemma deriv_eq_smul_circle_integral {R : ℝ} {c : ℂ} {f : ℂ → E} (hR : 0 < R)
  (hd : differentiable_on ℂ f (closed_ball c R)) :
  deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z :=
begin
  lift R to ℝ≥0 using hR.le,
  refine (hd.has_fpower_series_on_ball hR).has_fpower_series_at.deriv.trans _,
  simp only [cauchy_power_series_apply, one_div, zpow_neg₀, pow_one, smul_smul,
    zpow_two, mul_inv₀]
end

/-- If `f` is complex differentiable on a closed disc of radius `R`, and its values on the boundary
circle of this disc are bounded from above by `C`, then the norm of its derivative at the center
is at most `C / R`. -/
lemma norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → E} (hR : 0 < R)
  (hd : differentiable_on ℂ f (closed_ball c R)) (hC : ∀ z ∈ sphere c R, ∥f z∥ ≤ C) :
  ∥deriv f c∥ ≤ C / R :=
have ∀ z ∈ sphere c R, ∥(z - c) ^ (-2 : ℤ) • f z∥ ≤ C / (R * R),
  from λ z (hz : abs (z - c) = R), by simpa [norm_smul, hz, zpow_two, ← div_eq_inv_mul]
    using (div_le_div_right (mul_pos hR hR)).2 (hC z hz),
calc ∥deriv f c∥ = ∥(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z∥ :
  congr_arg norm (deriv_eq_smul_circle_integral hR hd)
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
    norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.differentiable_on (λ z _, hC z)
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

lemma norm_eq_norm_of_differentiable_on_of_is_max_on_closed_ball_of_mem_closed_ball {f : ℂ → E}
  {c w : ℂ} {R : ℝ} (hd : differentiable_on ℂ f (closed_ball c R))
  (hn : is_max_on (norm ∘ f) (closed_ball c R) c) (hw : w ∈ closed_ball c R) :
  ∥f w∥ = ∥f c∥ :=
begin
  refine (is_max_on_iff.1 hn _ hw).antisymm (not_lt.1 _),
  rintro hw_lt : ∥f w∥ < ∥f c∥,
  set r := dist w c,
  have hr : 0 < r, from dist_pos.2 (λ h, hw_lt.ne $ h ▸ rfl),
  have hsub' : closed_ball c r ⊆ closed_ball c R, from closed_ball_subset_closed_ball hw,
  have hsub : sphere c r ⊆ closed_ball c R, from sphere_subset_closed_ball.trans hsub',
  have hne : ∀ z ∈ sphere c r, z ≠ c,
    from λ z hz, ne_of_mem_of_not_mem hz (ne_of_lt $ (dist_self c).symm ▸ hr),
  have hcont : continuous_on (λ z, (z - c)⁻¹ • f z) (sphere c r),
    from ((continuous_on_id.sub continuous_on_const).inv₀ $
      λ z hz, sub_ne_zero.2 (hne z hz)).smul (hd.continuous_on.mono hsub),
  have hle : ∀ z ∈ sphere c r, ∥(z - c)⁻¹ • f z∥ ≤ ∥f c∥ / r,
  { rintros z (hz : abs (z - c) = r),
    simpa [norm_smul, hz, ← div_eq_inv_mul] using (div_le_div_right hr).2 (hn (hsub hz)) },
  have hlt : ∥(w - c)⁻¹ • f w∥ < ∥f c∥ / r,
    by simpa [norm_smul, ← div_eq_inv_mul] using (div_lt_div_right hr).2 hw_lt,
  have : ∥∮ z in C(c, r), (z - c)⁻¹ • f z∥ < 2 * π * r * (∥f c∥ / r),
    from circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr hcont hle ⟨w, rfl, hlt⟩,
  refine this.ne _,
  rw circle_integral_sub_inv_smul_of_differentiable_on (mem_ball_self hr) (hd.mono hsub'),
  field_simp [norm_smul, hr.ne', abs_of_pos real.pi_pos],
  ac_refl
end

lemma norm_eventually_eq_of_eventually_differentiable_at_of_is_local_max {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ∥f y∥ = ∥f c∥ :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, λ w hw,
    norm_eq_norm_of_differentiable_on_of_is_max_on_closed_ball_of_mem_closed_ball
      (λ z hz, (hr hz).1.differentiable_within_at) (λ z hz, (hr hz).2) hw⟩
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

end complex
