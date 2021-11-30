/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.complex_lebesgue
import measure_theory.integral.divergence_theorem
import analysis.analytic.basic
import analysis.calculus.parametric_interval_integral

/-!
# Cauchy integral formula

In this file we prove Cauchy theorem and Cauchy integral formula.
-/

open topological_space set measure_theory interval_integral metric filter function
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u v

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

/-- Let `f` be a function complex differentiable on the annulus `r ≤ |z| ≤ R`. Then the integrals
$\int_{|z|=r} f(z)\,d(\arg z)$ and $\int_{|z|=R} f(z)\,d(\arg z)$ are equal to each other. Moreover,
the same is true if at the points of some countable set, the function `f` is only continuous.

Up to a rescaling, these integrals are equal to $\int_{|z|=r}\frac{f(z)dz}{z}$ and
$\int_{|z|=R}\frac{f(z)dz}{z}$. -/
lemma integral_circle_darg_eq_of_differentiable_on_annulus_off_countable
  {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball 0 R \ ball 0 r) z)
  (hd : ∀ z ∈ (closed_ball 0 R \ ball 0 r) \ s,
    differentiable_within_at ℂ f (closed_ball 0 R \ ball 0 r) z) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = ∫ (θ : ℝ) in 0..2 * π, f (r * exp (θ * I)) :=
begin
  set A := closed_ball (0 : ℂ) R \ ball 0 r,
  obtain ⟨a, rfl⟩ : ∃ a, real.exp a = r, from ⟨real.log r, real.exp_log h0⟩,
  obtain ⟨b, rfl⟩ : ∃ b, real.exp b = R, from ⟨real.log R, real.exp_log (h0.trans_le hle)⟩,
  simp only [of_real_exp, ← exp_add], rw [real.exp_le_exp] at hle,
  replace hs : countable (exp ⁻¹' s) := hs.preimage_cexp,
  set R := re ⁻¹' [a, b] ∩ im ⁻¹' [0, 2 * π],
  have h_maps : maps_to exp R A,
  { rintro z ⟨h, -⟩, simpa [abs_exp, hle] using h.symm },
  replace hc : ∀ z ∈ exp ⁻¹' s, continuous_within_at (f ∘ exp) R z,
    from λ z hz, (hc (exp z) hz).comp continuous_within_at_id.cexp h_maps,
  replace hd : ∀ z ∈ R \ exp ⁻¹' s, differentiable_within_at ℂ (f ∘ exp) R z,
  { intros z hz,
    exact (hd (exp z) ⟨h_maps hz.1, hz.2⟩).comp z differentiable_within_at_id.cexp h_maps  },
  simpa [exp_periodic _, sub_eq_zero, (smul_right_injective E I_ne_zero).eq_iff]
    using integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩
      _ hs hc hd
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is differentiable on a
punctured closed disc of radius `R` and has a limit `y` at the center of the disc, then the integral
$\int_{|z|=R} f(z)\,d(\arg z)=-i\int_{|z|=R}\frac{f(z)\,dz}{z}$ is equal to $2πy`. Moreover, the
same is true if at the points of some countable set, `f` is only continuous, not differentiable. -/
lemma integral_circle_darg_of_differentiable_on_off_countable_of_tendsto
  {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball 0 R \ {0}) z)
  (hd : ∀ z ∈ closed_ball 0 R \ {(0 : ℂ)} \ s,
    differentiable_within_at ℂ f (closed_ball 0 R \ {0}) z)
  (hy : tendsto f (𝓝[{0}ᶜ] 0) (𝓝 y)) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = (2 * π) • y :=
begin
  rw [← sub_eq_zero, ← norm_le_zero_iff],
  refine le_of_forall_le_of_dense (λ ε ε0, _),
  obtain ⟨δ, δ0, hδ⟩ :
    ∃ δ > (0 : ℝ), ∀ z ∈ closed_ball (0 : ℂ) δ \ {0}, dist (f z) y < ε / (2 * π),
    from ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 real.two_pi_pos),
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩,
  have hsub : closed_ball (0 : ℂ) R \ ball 0 r ⊆ closed_ball 0 R \ {(0 : ℂ)},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_ball_self hr0),
  have : ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = ∫ (θ : ℝ) in 0..2 * π, f (r * exp (θ * I)),
  { refine integral_circle_darg_eq_of_differentiable_on_annulus_off_countable hr0 hrR hs _ _,
    exacts [λ z hz, (hc z hz).mono hsub, λ z hz, (hd z ⟨hsub hz.1, hz.2⟩).mono hsub] },
  rw this,
  have hmem : ∀ y : ℝ, ↑r * exp (y * I) ∈ closed_ball (0 : ℂ) r \ {0},
  { intro x, simp [abs_of_nonneg hr0.le, hr0.ne', exp_ne_zero] },
  have : ∫ (θ : ℝ) in 0..2 * π, y = (2 * π) • y := by simp,
  rw [← this, ← interval_integral.integral_sub],
  { have : ∀ x : ℝ, ∥f (r * exp (x * I)) - y∥ ≤ ε / (2 * π),
    { intro x, rw ← dist_eq_norm,
      exact (hδ _ (diff_subset_diff_left (closed_ball_subset_closed_ball hrδ) (hmem x))).le },
    refine (interval_integral.norm_integral_le_of_norm_le_const (λ x _, this x)).trans_eq _,
    simp [real.two_pi_pos.ne', _root_.abs_of_nonneg real.two_pi_pos.le] },
  { refine continuous.interval_integrable _ _ _,
    have : continuous_on f (closed_ball 0 R \ {0}),
    { intros z hz, by_cases hzs : z ∈ s,
      exacts [hc z hzs, (hd z ⟨hz, hzs⟩).continuous_within_at] },
    refine this.comp_continuous _ _,
    { continuity },
    { exact λ y, ⟨closed_ball_subset_closed_ball hrR (hmem y).1, (hmem y).2⟩ } },
  { simp [interval_integrable, measure_lt_top] }
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is differentiable on a
closed disc of radius `R`, then the integral
$\int_{|z|=R} f(z)\,d(\arg z)=-i\int_{|z|=R}\frac{f(z)\,dz}{z}$ is equal to $2πy`. Moreover, the
same is true if at the points of some countable set, `f` is only continuous, not differentiable. -/
lemma integral_circle_darg_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {s : set ℂ} (hs : countable s) (hc : ∀ x ∈ s, continuous_within_at f (closed_ball 0 R) x)
  (hd : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ f (closed_ball 0 R) z) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = (2 * π) • f 0 :=
begin
  rcases h0.eq_or_lt with (rfl|h0), { simp },
  refine integral_circle_darg_of_differentiable_on_off_countable_of_tendsto h0 hs
    (λ z hz, (hc z hz).mono $ diff_subset _ _)
    (λ z hz, (hd z ⟨hz.1.1, hz.2⟩).mono $ diff_subset _ _) _,
  suffices : continuous_within_at f (closed_ball 0 R) 0,
    from (this.continuous_at (closed_ball_mem_nhds _ h0)).continuous_within_at,
  by_cases h : (0 : ℂ) ∈ s,
  exacts [hc _ h, (hd _ ⟨mem_closed_ball_self h0.le, h⟩).continuous_within_at]
end

/-- **Cauchy theorem**: the integral of a complex differentiable function over the boundary of a
disc equals zero. Moreover, the same is true if at the points of some countable set, `f` is only
continuous. -/
lemma integral_circle_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {s : set ℂ} (hs : countable s) (hc : ∀ x ∈ s, continuous_within_at f (closed_ball 0 R) x)
  (hd : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ f (closed_ball 0 R) z) :
  ∫ (θ : ℝ) in 0..2 * π, (R * exp (θ * I) * I : ℂ) • f (R * exp (θ * I)) = 0 :=
by simpa [mul_smul, smul_comm _ I, interval_integral.integral_smul, I_ne_zero]
  using integral_circle_darg_of_differentiable_on_off_countable h0 hs
    (λ z hz, continuous_within_at_id.smul (hc z hz))
    (λ z hz, differentiable_within_at_id.smul (hd z hz))

/-- If `|w|<R` and `n ≠ -1`, then $\int_{|z|=R} (z-w)^n\,dz=0`. -/
lemma integral_circle_zpow_sub_of_abs_lt {R : ℝ} {w : ℂ} (hw : abs w < R) {n : ℤ} (hn : n ≠ -1) :
  ∫ θ : ℝ in 0..2 * π, ↑R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ n = 0 :=
begin
  have hR0 : 0 < R := (abs_nonneg w).trans_lt hw,
  have h0 : ∀ θ : ℝ, ↑R * exp (θ * I) - w ≠ 0,
  { refine λ θ, sub_ne_zero.2 (λ h₀, _),
    simpa [h₀.symm, _root_.abs_of_nonneg hR0.le] using hw },
  set f : ℝ → ℂ := λ θ, R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ n,
  set F : ℝ → ℂ := λ θ, (R * exp (θ * I) - w) ^ (n + 1) / (n + 1),
  have : ∀ θ, has_deriv_at F (f θ) θ,
  { intro θ, simp only [F, div_eq_mul_inv],
    convert (((has_deriv_at_zpow (n + 1) _
      (or.inl $ h0 θ)).has_fderiv_at.restrict_scalars ℝ).comp_has_deriv_at θ
      (((of_real_clm.has_deriv_at.mul_const I).cexp_real.const_mul ↑R).sub_const w)).mul_const _,
    have : (n + 1 : ℂ) ≠ 0, by exact_mod_cast mt eq_neg_iff_add_eq_zero.2 hn,
    field_simp [f, this], ac_refl },
  have hfc : continuous f,
  { have : continuous (λ θ : ℝ, ↑R * exp (θ * I)) :=
      continuous_const.mul (continuous_of_real.mul continuous_const).cexp,
    exact (this.mul continuous_const).mul ((this.sub continuous_const).zpow _
      (λ θ, or.inl (h0 θ))) },
  calc ∫ θ in 0 .. 2 * π, f θ = F (2 * π) - F 0 :
    interval_integral.integral_eq_sub_of_has_deriv_at (λ θ _, this θ) (hfc.interval_integrable _ _)
  ... = 0 : by { simp only [F], simp }
end

def cauchy_power_series (f : ℝ → E) (R : ℝ) :
  formal_multilinear_series ℂ ℂ E :=
λ n, continuous_multilinear_map.mk_pi_field ℂ _ $
  ∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I))⁻¹ ^ n • f θ

lemma cauchy_power_series_apply (f : ℝ → E) (R : ℝ) (n : ℕ) (z : ℂ) :
  cauchy_power_series f R n (λ _, z) =
    ∫ θ : ℝ in 0..2*π, (z / (R * exp (θ * I))) ^ n • f θ :=
by simp only [cauchy_power_series, continuous_multilinear_map.mk_pi_field_apply, fin.prod_const,
  ← interval_integral.integral_smul, div_eq_mul_inv, mul_pow, smul_smul]

lemma norm_cauchy_power_series_le (f : ℝ → E) (R : ℝ) (n : ℕ) :
  ∥cauchy_power_series f R n∥ ≤ (∫ θ : ℝ in 0..2*π, ∥f θ∥) * (|R|⁻¹) ^ n :=
begin
  simp only [cauchy_power_series, continuous_multilinear_map.norm_mk_pi_field],
  refine (interval_integral.norm_integral_le_integral_norm real.two_pi_pos.le).trans_eq _,
  conv_rhs { rw [mul_comm, ← interval_integral.integral_const_mul] },
  simp only [norm_smul, abs_of_real, mul_one, abs_mul, abs_exp_of_real_mul_I, abs_inv,
    abs_pow, norm_eq_abs]
end

lemma le_radius_cauchy_power_series (f : ℝ → E) (R : ℝ≥0) :
  ↑R ≤ (cauchy_power_series f R).radius :=
begin
  refine (cauchy_power_series f R).le_radius_of_bound (∫ θ : ℝ in 0..2*π, ∥f θ∥) (λ n, _),
  refine (mul_le_mul_of_nonneg_right (norm_cauchy_power_series_le _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans _,
  rw [_root_.abs_of_nonneg R.coe_nonneg],
  cases eq_or_ne (R ^ n : ℝ) 0 with hR hR,
  { rw [hR, mul_zero],
    exact interval_integral.integral_nonneg real.two_pi_pos.le (λ _ _, norm_nonneg _) },
  { rw [inv_pow₀, inv_mul_cancel_right₀ hR] }
end

lemma has_sum_cauchy_power_series_integral {f : ℝ → E} {R : ℝ} {z : ℂ}
  (hf : interval_integrable f volume 0 (2 * π)) (hR : abs z < R) :
  has_sum (λ n, cauchy_power_series f R n (λ _, z))
    (∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I) / (R * exp (θ * I) - z)) • f θ) :=
begin
  have hR0 : 0 < R := (abs_nonneg z).trans_lt hR,
  have hzR : abs z / R ∈ Ico (0 : ℝ) 1,
    from ⟨div_nonneg (abs_nonneg z) hR0.le, (div_lt_one hR0).2 hR⟩,
  simp only [cauchy_power_series_apply],
  refine interval_integral.has_sum_integral_of_dominated_convergence
    (λ n t, ∥f t∥ * (abs z / R) ^ n) (λ n, _) (λ n, _) _ _ _,
  { exact ((((measurable_of_real.mul_const _).cexp.const_mul _).const_div _).pow_const
        _).ae_measurable.smul hf.def.ae_measurable },
  { simp [norm_smul, _root_.abs_of_nonneg hR0.le, mul_comm (∥f _∥)] },
  { exact eventually_of_forall (λ t ht, (summable_geometric_of_lt_1 hzR.1 hzR.2).mul_left _) },
  { simp only [tsum_mul_left, tsum_geometric_of_lt_1 hzR.1 hzR.2,
      hf.norm.mul_continuous_on continuous_on_const] },
  { refine eventually_of_forall (λ θ hθ, _),
    have : ∥z / (R * exp (θ * I))∥ < 1, by simpa [_root_.abs_of_nonneg hR0.le] using hzR.2,
    convert (has_sum_geometric_of_norm_lt_1 this).smul_const; [skip, apply_instance],
    have : ↑R * exp (θ * I) ≠ 0 := mul_ne_zero (of_real_ne_zero.2 hR0.ne') (exp_ne_zero _),
    field_simp [this] }
end

lemma sum_cauchy_power_series_eq_integral {f : ℝ → E} {R : ℝ} {z : ℂ}
  (hf : interval_integrable f volume 0 (2 * π)) (hR : abs z < R) :
  (cauchy_power_series f R).sum z =
    ∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I) / (R * exp (θ * I) - z)) • f θ :=
(has_sum_cauchy_power_series_integral hf hR).tsum_eq

lemma has_fpower_series_on_cauchy_integral {f : ℝ → E} {R : ℝ≥0} {z : ℂ}
  (hf : interval_integrable f volume 0 (2 * π)) (hR : 0 < R) :
  has_fpower_series_on_ball
    (λ z, ∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I) / (R * exp (θ * I) - z)) • f θ)
    (cauchy_power_series f R) 0 R :=
{ r_le := le_radius_cauchy_power_series _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ y hy,
    begin
      rw zero_add,
      refine has_sum_cauchy_power_series_integral hf _,
      rw [← norm_eq_abs, ← coe_nnnorm, nnreal.coe_lt_coe, ← ennreal.coe_lt_coe],
      exact mem_emetric_ball_zero_iff.1 hy
    end }

lemma integral_circle_div_sub_of_abs_lt {R : ℝ} {w : ℂ} (hw : abs w < R) :
  ∫ θ : ℝ in 0..2 * π, (↑R * exp (θ * I) * I / (R * exp (θ * I) - w)) = 2 • π • I :=
begin
  have A : interval_integrable (λ _, I) volume (0 : ℝ) (2 * π), from interval_integrable_const,
  have B := has_sum_cauchy_power_series_integral A hw,
  simp only [cauchy_power_series_apply, smul_eq_mul, ← mul_div_right_comm] at B,
  refine B.unique _, clear A B,
  have : ∫ θ : ℝ in 0..2*π, (w / (R * exp (θ * I))) ^ 0 * I = 2 • π • I, by simp [mul_assoc],
  refine this ▸ has_sum_single _ (λ n hn, _),
  suffices : ∫ θ : ℝ in 0..2 * π, (↑R * exp (↑θ * I))⁻¹ ^ n * I = 0,
    by simp only [div_eq_mul_inv, mul_pow w, interval_integral.integral_const_mul, this,
      mul_assoc, mul_zero],
  replace hn : (-n : ℤ) - 1 ≠ -1, by simpa [sub_eq_iff_eq_add],
  have hR0 : 0 < R := (abs_nonneg w).trans_lt hw,
  have hR0' : abs 0 < R, by rwa abs_zero,
  have h0 : ∀ θ : ℝ, ↑R * exp (θ * I) ≠ 0,
    from λ θ, mul_ne_zero (of_real_ne_zero.2 hR0.ne') (exp_ne_zero _),
  have := integral_circle_zpow_sub_of_abs_lt hR0' hn,
  simp only [← neg_add', zpow_neg₀, sub_zero, ← int.coe_nat_succ, zpow_coe_nat, ← inv_pow₀,
    pow_succ, ← div_eq_mul_inv] at this,
  simpa only [mul_div_right_comm _ I, div_mul_right _ (h0 _), one_div, inv_pow₀] using this
end

lemma integral_circle_div_sub_of_differentiable_on₀ {R : ℝ} {w : ℂ} (hw : abs w < R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball 0 R)) :
  ∫ (θ : ℝ) in 0..2 * π, ((R * exp (θ * I) * I) / (R * exp (θ * I) - w) : ℂ) • f (R * exp (θ * I)) =
    2 • π • I • f w :=
begin
  set F : ℂ → E := update (λ z, (z - w)⁻¹ • (f z - f w)) w (deriv f w),
  set s : set ℂ := {w},
  have hnhds : closed_ball (0 : ℂ) R ∈ 𝓝 w,
    from _root_.mem_nhds_iff.2 ⟨ball 0 R, ball_subset_closed_ball, is_open_ball, by simpa⟩,
  have hc : ∀ z ∈ s, continuous_within_at F (closed_ball 0 R) z,
  { rintro z (rfl|_),
    have := has_deriv_at_iff_tendsto_slope.1 (hd.has_deriv_at hnhds),
    rw [← continuous_within_at_diff_self, continuous_within_at],
    simp only [F, update_same],
    refine (this.congr' _).mono_left (nhds_within_mono _ (inter_subset_right _ _)),
    filter_upwards [self_mem_nhds_within] (λ z hz, (update_noteq hz _ _).symm) },
  have hdF : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ F (closed_ball 0 R) z,
  { rintro z ⟨hzR, hzw : z ≠ w⟩,
    refine (((differentiable_within_at_id.sub_const w).inv $ sub_ne_zero.2 hzw).smul
      ((hd z hzR).sub_const (f w))).congr_of_eventually_eq _ _,
    { filter_upwards [mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds hzw)],
      exact λ x hx, update_noteq hx _ _ },
    { exact update_noteq hzw _ _ } },
  have HI := integral_circle_eq_zero_of_differentiable_on_off_countable ((abs_nonneg w).trans hw.le)
    (countable_singleton w) hc hdF,
  have hF : ∀ θ : ℝ, F (↑R * exp (θ * I)) = (↑R * exp (θ * I) - w)⁻¹ • (f (R * exp (θ * I)) - f w),
  { refine λ θ, update_noteq _ _ _,
    rintro rfl, simpa [abs_exp, (le_abs_self R).not_lt] using hw },
  simp only [hF, smul_sub, ← div_eq_mul_inv, smul_smul] at HI ⊢,
  have hc₁ : continuous (λ θ, R * exp (θ * I) : ℝ → ℂ),
    from continuous_const.mul (continuous_of_real.mul continuous_const).cexp,
  have hR0 : 0 < R := (abs_nonneg w).trans_lt hw,
  have hne : ∀ θ : ℝ, ↑R * exp (θ * I) - w ≠ 0,
  { refine λ θ, sub_ne_zero.2 _, rintro rfl, simpa [hR0.le] using hw.ne },
  have hc₂ : continuous (λ θ, R * exp (θ * I) * I / (R * exp (θ * I) - w) : ℝ → ℂ),
    from (hc₁.mul continuous_const).div (hc₁.sub continuous_const) hne,
  have hfc : continuous (λ θ, f (R * exp (θ * I)) : ℝ → E),
  { refine hd.continuous_on.comp_continuous hc₁ (λ θ, _),
    simp [_root_.abs_of_nonneg hR0.le] },
  rw [interval_integral.integral_sub, sub_eq_zero] at HI,
  { rw [HI, interval_integral.integral_smul_const],
    simp_rw [integral_circle_div_sub_of_abs_lt hw, smul_assoc] },
  exacts [(hc₂.smul hfc).interval_integrable _ _,
    (hc₂.smul continuous_const).interval_integrable _ _]
end

lemma integral_circle_div_sub_of_differentiable_on {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball z R)) :
  ∫ (θ : ℝ) in 0..2 * π,
    ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w) : ℂ) • f (z + R * exp (θ * I)) =
    2 • π • I • f w :=
begin
  rw [mem_ball, dist_eq] at hw,
  replace hd : differentiable_on ℂ (λ ζ, f (z + ζ)) (closed_ball 0 R),
  { refine hd.comp (differentiable_on_id.const_add _) _,
    rw [preimage_add_closed_ball, sub_self] },
  simpa only [add_sub_cancel'_right, sub_sub_assoc_swap, add_comm _ z]
    using integral_circle_div_sub_of_differentiable_on₀ hw hd
end

lemma holo_test {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball z R)) :

  f w  = (1/(2 • π • I)) • ∫ (θ : ℝ) in 0..2 * π,
    ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w) : ℂ) • f (z + R * exp (θ * I)) :=

begin
have := integral_circle_div_sub_of_differentiable_on hw hd,
simp only [this, one_div, nat.cast_bit0, real_smul, nsmul_eq_mul, nat.cast_one],
simp_rw ← smul_assoc,
simp,
simp_rw ← mul_assoc,
have hn : (2 * ↑π * I) ≠ 0, by {simp, simp [real.pi_ne_zero, complex.I_ne_zero],},
have tt := inv_mul_cancel hn,
simp_rw ← mul_assoc at tt,
rw tt,
simp,
end



def int_diff0 (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ): (ℝ → E) :=
λ θ, (1/(2 • π • I)) • ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w) : ℂ) • f (z + R * exp (θ * I))

lemma int_diff0_cont (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ) (hf : continuous f) (hw : w ∈ ball z R):
  continuous (int_diff0 R hR f z w) :=
begin
  rw int_diff0,
  simp,
  apply continuous.smul,
  exact continuous_const,
  apply continuous.smul,
  apply continuous.div,
  sorry,
sorry,
sorry,
sorry,
end



def int_diff0' (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ): (ℝ → E) :=
λ θ, (1/(2 • π • I)) • ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w)^2 : ℂ) • f (z + R * exp (θ * I))

def int_diff (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z : ℂ)
   : (ℂ → E) := λ w,  ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR f z w θ)

def int_diff' (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z : ℂ)
   : (ℂ → E) := λ w,  ∫ (θ : ℝ) in 0..2 * π, (int_diff0' R hR f z w θ)

lemma int_diff_has_fdrevi (R : ℝ)  (hR: 0 < R) (z : ℂ) (f : ℂ → ℂ)  (hf: continuous f) :
  differentiable_on ℂ (int_diff R hR f z) (ball z R) :=
begin
rw int_diff,
simp_rw int_diff0,
rw differentiable_on,
simp_rw differentiable_within_at,
intros x hx,
set F: ℂ → ℝ → ℂ  := λ w, (λ θ, (int_diff0 R hR f z w θ)),
set F': ℂ → ℝ → ℂ := λ w, (λ θ, (int_diff0' R hR f z w θ)),
have hF_meas : ∀ᶠ y in 𝓝 x, ae_measurable (F y) (volume.restrict (Ι 0 (2 * π))) ,
by {simp_rw F,
    have : ∀ (y : ℂ), ae_measurable (int_diff0 R hR f z y) (volume.restrict (Ι 0 (2 * π))),
    by {intro y,
    have := continuous.ae_measurable (int_diff0_cont R hR f z y hf _),
    apply ae_measurable.restrict,
    apply this, sorry,},
    simp [this],
    },
have hF_int : interval_integrable (F x) volume 0  (2 * π),
by {simp_rw F,
  have := continuous.interval_integrable (int_diff0_cont R hR f z x hf hx) 0 (2*π),
  apply this,
  apply_instance,},
have  hF'_meas : ae_measurable (F' x) (volume.restrict (Ι 0 (2 * π))) , by {sorry},
set bound : ℝ → ℝ := λ r, ∥F' R r∥,
have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x R, ∥F' y t∥ ≤  bound t, by {sorry},
have  bound_integrable : interval_integrable bound volume 0 (2 * π) , by {sorry},
have h_diff : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x R, has_deriv_at (λ y, F y t) (F' y t) y,
by {sorry},
have := interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le hR hF_meas hF_int hF'_meas
  h_bound bound_integrable h_diff,
simp_rw F at this,
simp_rw int_diff0 at this,
simp_rw has_deriv_at at this,
simp_rw has_deriv_at_filter at this,
simp_rw has_fderiv_within_at,
simp at *,
have h3:= this.2,
let der := (interval_integral (F' x) 0 (2 * π) volume),
let DER := continuous_linear_map.smul_right (1 : ℂ →L[ℂ] ℂ) der,
use DER,
simp_rw [DER, der],
have this2:= (has_fderiv_at_filter.mono h3),
apply this2,
rw nhds_within,
simp [inf_le_left],
end



lemma int_diff0_int (R : ℝ) (hR: 0 < R) (F : ℂ → ℂ) (F_cts :  continuous (F ))
  (z : ℂ) (w : ball z R): integrable (int_diff0 R hR (F) z w) (volume.restrict (Ioc 0  (2*π))) :=

begin
apply integrable_on.integrable,
rw ←  interval_integrable_iff_integrable_Ioc_of_le,
apply continuous_on.interval_integrable,
have hw:= w.property,
simp at hw,
have := int_diff0_cont R hR F z w F_cts,
simp at this,
have hc:= this hw,
apply continuous.continuous_on,
apply hc,
simp,
linarith [real.pi_pos],
end

lemma UNIF_CONV_INT (R : ℝ) (hR: 0 < R) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)  (F_cts : ∀ n, continuous (F n))
   (hlim : tendsto_uniformly F f filter.at_top) (z : ℂ) (w : ball z R) :
tendsto (λn, ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR (F n) z w) θ)
  at_top (𝓝 $  ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR f z w) θ) :=

begin
have f_cont: continuous f, by {sorry,},

have F_measurable : ∀ n, ae_measurable (int_diff0 R hR (F n) z w) (volume.restrict (Ioc 0  (2*π))),
 by {intro n,
     have:= int_diff0_int R hR (F n) (F_cts n) z w,
     apply this.ae_measurable, },


have h_lim'' : ∀ (a : ℝ), tendsto (λ n, ((int_diff0 R hR (F n) z w)) a)
  at_top (𝓝 (((int_diff0 R hR f z w)) a)),

 by {rw metric.tendsto_uniformly_iff at hlim, simp_rw metric.tendsto_nhds, simp_rw  dist_comm,
  simp_rw int_diff0,
  simp at *,
  intros y ε hε,
  set r : ℂ :=  ((2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w))),
  have hr: 0 < ∥ r ∥, by {simp, rw div_eq_inv_mul,
    apply mul_pos, rw inv_eq_one_div, rw one_div_pos,
    apply mul_pos, linarith, simp, apply real.pi_ne_zero,
    apply mul_pos,
    rw inv_pos,
    rw abs_pos,
    have hw:=w.property,
    simp at hw,
    by_contradiction hc,
    simp_rw dist_eq_norm at hw,
    have hc' : (w : ℂ)-z = R * exp (↑y * I), by {sorry,},
     simp_rw hc' at hw,
     simp at hw,
     rw abs_lt at hw,
     simp at hw,
     apply hw,
     simp,
     by_contradiction hrr,
     rw hrr at hR,
     simp at hR,
     apply hR,},
  have hr':  ∥ r ∥ ≠ 0, by {linarith,},
  let e:= (∥ r ∥)⁻¹ * (ε/2),
  have he: 0 < e, by {sorry,},
  have h_lim2:= hlim e he,
  obtain ⟨a, ha⟩ := h_lim2,
  use a,
  intros b hb,
  simp [ha b hb],
  simp_rw dist_eq_norm at *,
  simp_rw ← mul_sub,
  have hg: ∥(2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w) *
    (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))))∥ =
    ∥(2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w)) ∥ *
    ∥ (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I)))∥, by {simp, ring,},
    rw hg,
    simp_rw ← r,
    have haa:= ha b hb,
    have hab:= haa (z + ↑R * exp (↑y * I)),
    have haav: ∥ r ∥ * ∥f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))∥ < ∥ r ∥ * e,
    by {apply mul_lt_mul_of_pos_left hab hr,},
    simp_rw e at haav,
    apply lt_trans haav,
    rw div_eq_inv_mul,
    simp_rw ← mul_assoc,
    simp_rw [mul_inv_cancel hr'],
    simp,
    rw  mul_lt_iff_lt_one_left,
    rw inv_eq_one_div,
    linarith,
    apply hε,},

have h_lim' : ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))), tendsto (λ n, ((int_diff0 R hR (F n) z w)) a)
  at_top (𝓝 (((int_diff0 R hR f z w)) a)),
  by {simp [h_lim''],},
rw metric.tendsto_uniformly_iff at hlim,
simp at hlim,
have hlimb:= hlim 1 (zero_lt_one),
obtain ⟨ a, ha⟩ :=hlimb,
set bound: ℝ → ℝ :=λ θ, (∑ (i : finset.range (a+1) ),complex.abs ((int_diff0 R hR (F i) z w) θ))  +
complex.abs ((int_diff0 R hR (λ x, 1) z w) θ)  + complex.abs ((int_diff0 R hR f z w) θ),

have h_bound : ∀ n, ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))), ∥(int_diff0 R hR (F n) z w) a∥ ≤ bound a,
by {
  intro n,
  rw  ae_restrict_iff' at *,
  rw eventually_iff_exists_mem,
  use ⊤,
  simp,
  intros y hyl hyu,
  by_cases (n ≤ a),
  simp_rw bound,
  sorry,
  simp at h,
  sorry,
  all_goals {simp only [measurable_set_Ioc]},},


have bound_integrable : integrable bound (volume.restrict (Ioc 0  (2*π))), by {sorry,},
have := tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable h_bound h_lim',
have pi: 0 ≤ 2*π , by {sorry},
simp_rw  integral_of_le pi,
apply this,
end




protected lemma _root_.differentiable_on.has_fpower_series_on_ball {R : ℝ≥0} {z : ℂ} {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball z R)) (hR : 0 < R) :
  has_fpower_series_on_ball f
    (cauchy_power_series (λ θ, (2 * π)⁻¹ • f (z + R * exp (θ * I))) R) z R :=
{ r_le := le_radius_cauchy_power_series _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ w hw,
    begin
      rw [mem_emetric_ball_zero_iff, ennreal.coe_lt_coe, ← nnreal.coe_lt_coe, coe_nnnorm,
        norm_eq_abs] at hw,
      replace hd : differentiable_on ℂ (λ ζ, f (z + ζ)) (closed_ball 0 R),
      { refine hd.comp (differentiable_on_id.const_add _) _,
        rw [preimage_add_closed_ball, sub_self] },
      have hfi : interval_integrable (λ θ : ℝ, (2 * π)⁻¹ • f (z + R * exp (θ * I))) volume 0 (2 * π),
      { refine (continuous_const.smul $
          hd.continuous_on.comp_continuous _ $ λ θ, _).interval_integrable _ _,
        { exact continuous_const.mul (continuous_of_real.mul continuous_const).cexp },
        { simp } },
      convert ← has_sum_cauchy_power_series_integral hfi hw using 1,
      convert integral_circle_div_sub_of_differentiable_on₀ hw
        (hd.const_smul (2 * π * I : ℂ)⁻¹) using 2,
      { simp_rw [mul_div_right_comm _ I, ← coe_smul, smul_smul, of_real_inv, of_real_mul, coe_coe,
          of_real_bit0, of_real_one, mul_inv_rev₀, mul_assoc, mul_inv_cancel_left₀ I_ne_zero] },
      { simp_rw [← coe_smul, two_smul, ← @two_smul ℂ E, smul_smul, ← mul_assoc],
        rw [mul_inv_cancel, one_smul], simp [I_ne_zero, real.pi_ne_zero] }
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

lemma unif_of_diff_is_diff (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R : ℝ)  (hR: 0 < R)
  (hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (closed_ball z R))
  (hlim : tendsto_uniformly F f filter.at_top) :
  differentiable_on ℂ f (ball z R) :=
begin
have F_measurable : ∀ n, integrable (F n) volume, by {sorry,},
have F_cts : ∀ n, continuous (F n) , by {sorry,},
rw differentiable_on,
intros x hx,
have key:= UNIF_CONV_INT R hR F f F_cts hlim z ⟨x, hx⟩,
--have key := int_diff_of_uniform' F f z x R hR hlim,
rw differentiable_within_at,
have h0:= int_diff R hR f z,
--have h1:= holo_test hx (hdiff _),
have hf: continuous f, by {sorry,},
have HF:= int_diff_has_fdrevi R hR x f hf,
rw differentiable_on at HF,
have HF2:= HF x,
simp [hx, hR] at HF2,
rw differentiable_within_at at HF2,
obtain ⟨D, hD⟩:= HF2,
use D,
simp_rw has_fderiv_within_at_iff_tendsto at *,
rw metric.tendsto_nhds at *,
rw tendsto_uniformly_iff at hlim,
simp_rw dist_eq_norm at *,
intros ε hε,
have hlim2:= hlim ε hε,
simp at *,
obtain ⟨a, ha⟩ := hlim2,
have HH: ∀ (y : ℂ), f y - f x - (D y - D x) =
(f y - F a y) - ((f x)- (F a x)) + ((F a y)- (F a x))  - (D y - D x), by {sorry,},
simp_rw HH,
rw int_diff at hD,
simp at hD,
sorry,
end


end complex
