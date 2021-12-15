import measure_theory.integral.interval_integral
import analysis.special_functions.non_integrable

/-!
-/

variables {E : Type*} [measurable_space E] [normed_group E]

noncomputable theory

open_locale real nnreal interval pointwise topological_space
open complex measure_theory topological_space metric function set filter

def circle_map (c : ℂ) (R : ℝ) : ℝ → ℂ := λ θ, c + R * exp (θ * I)

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

@[simp] lemma range_circle_map (c : ℂ) (R : ℝ) : range (circle_map c R) = sphere c (|R|) :=
calc range (circle_map c R) = c +ᵥ R • range (λ θ : ℝ, exp (θ * I)) :
  by simp only [← image_vadd, ← image_smul, ← range_comp, vadd_eq_add, circle_map, (∘), real_smul]
... = sphere c (|R|) : by simp [smul_sphere _ (0 : ℂ) zero_le_one, real.norm_eq_abs]

@[simp] lemma image_circle_map_Ioc (c : ℂ) (R : ℝ) :
  circle_map c R '' Ioc 0 (2 * π) = sphere c (|R|) :=
by rw [← range_circle_map, ← (periodic_circle_map c R).image_Ioc real.two_pi_pos 0, zero_add]

lemma circle_map_mem_closed_ball (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
  circle_map c R θ ∈ closed_ball c R :=
sphere_subset_closed_ball (circle_map_mem_sphere c hR θ)

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

lemma differentiable_circle_map (c : ℂ) (R : ℝ) :
  differentiable ℝ (circle_map c R) :=
λ θ, (has_deriv_at_circle_map c R θ).differentiable_at

lemma continuous_circle_map (c : ℂ) (R : ℝ) : continuous (circle_map c R) :=
(differentiable_circle_map c R).continuous

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

/-- The function we actually integrate over `[0, 2π]` is integrable. -/
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

/-
TODO
lemma circle_integrable_sub_zpow {c w : ℂ} {R : ℝ} {n : ℤ} :
  circle_integrable (λ z, (z - w) ^ n) c R ↔ R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c (|R|) :=
begin
  split,
  { intro h, contrapose! h, rcases h with ⟨hR, hn, hw⟩,
    simp only [circle_integrable_iff hR],
    rw ← image_circle_map_Ioc at hw, rcases hw with ⟨θ, hθ, rfl⟩,
    replace hθ : θ ∈ [0, 2 * π], from Icc_subset_interval (Ioc_subset_Icc_self hθ),
    rcases (int.le_sub_one_of_lt hn).eq_or_lt with rfl|hn,
    {  },
    }
end
-/

variables [normed_space ℂ E] [complete_space E] [borel_space E] [second_countable_topology E]

/-- Definition for $\int_{|w-c|=R} f(w)\,dw$. -/
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

@[simp] lemma integral_smul {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] [smul_comm_class 𝕜 ℝ E]
  [smul_comm_class 𝕜 ℂ E] (a : 𝕜) (f : ℂ → E) (c : ℂ) (R : ℝ) :
  ∮ z in C(c, R), a • f z = a • ∮ z in C(c, R), f z :=
by simp only [circle_integral, ← smul_comm a, interval_integral.integral_smul]

@[simp] lemma integral_smul_const (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
  ∮ z in C(c, R), (f z • a) = (∮ z in C(c, R), f z) • a :=
by simp only [circle_integral, interval_integral.integral_smul_const, ← smul_assoc]

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
integral_eq_zero_of_has_deriv_within_at' $ by simpa only [_root_.abs_of_nonneg hR] using h

/-- If  `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
lemma integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
  ∮ z in C(c, R), (z - w) ^ n = 0 :=
begin
  have hn' : (n + 1 : ℂ) ≠ 0,
    by rwa [ne, ← eq_neg_iff_add_eq_zero, ← int.cast_one, ← int.cast_neg, int.cast_inj],
  have hd : ∀ z, (z ≠ w ∨ -1 ≤ n) → has_deriv_at (λ z, (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z,
  { intros z hne,
    convert ((has_deriv_at_zpow (n + 1) _ (hne.imp _ _)).comp z
      ((has_deriv_at_id z).sub_const w)).div_const _ using 1,
    { simp [mul_assoc, mul_div_cancel_left _ hn'] },
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1] },
  have hd' : ∀ θ, circle_map c R θ ≠ w →
    has_deriv_at (λ θ, (circle_map c R θ - w) ^ (n + 1) / (n + 1))
      (deriv (circle_map c R) θ • (circle_map c R θ - w) ^ n) θ,
  { intros θ hne,
    rw [smul_eq_mul, mul_comm],
    exact (hd _ (or.inl hne)).comp θ (differentiable_circle_map c R θ).has_deriv_at },
  rcases em (w ∈ sphere c (|R|) ∧ n < -1) with ⟨hw, hn⟩|H,
  { -- In this case `(z - w) ^ n` is not circle integrable
    rcases eq_or_ne R 0 with rfl|h0, { apply integral_radius_zero },
    apply interval_integral.integral_undef,
    rw ← image_circle_map_Ioc at hw, rcases hw with ⟨θ, hθ, rfl⟩,
    replace hθ : θ ∈ [0, 2 * π], from Icc_subset_interval (Ioc_subset_Icc_self hθ),
    have hne : ∀ᶠ x in 𝓝[{θ}ᶜ] θ, circle_map c R x ≠ circle_map c R θ,
      from (differentiable_circle_map _ _ _).has_deriv_at.eventually_ne
        (deriv_circle_map_ne_zero h0),
    refine interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured
      real.two_pi_pos.ne hθ (hne.mono hd') _,
    simp only [normed_field.norm_div],
    refine tendsto.at_top_div_const (norm_pos_iff.2 hn') _,
    refine (normed_field.tendsto_norm_zpow_nhds_within_0_at_top $ lt_neg_iff_add_neg.1 hn).comp _,
    refine tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ _
      (hne.mono $ λ _, sub_ne_zero.2),
    exact (((differentiable_circle_map _ _).sub_const _).continuous.tendsto'
      _ _ (sub_self _)).mono_left inf_le_left },
  { push_neg at H,
    refine integral_eq_zero_of_has_deriv_within_at' (λ z hz, (hd z _).has_deriv_within_at),
    exact (ne_or_eq z w).imp_right (λ h, H $ h ▸ hz) }
end

end circle_integral
