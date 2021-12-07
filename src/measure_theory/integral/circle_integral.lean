import measure_theory.integral.interval_integral

/-!
-/

variables {E : Type*} [measurable_space E] [normed_group E]

noncomputable theory

open_locale real nnreal interval
open complex measure_theory topological_space metric function

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

lemma continuous_on.circle_integrable [borel_space E] {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
  (hf : continuous_on f (sphere c R)) :
  circle_integrable f c R :=
(hf.comp_continuous (continuous_circle_map _ _)
  (circle_map_mem_sphere _ hR)).interval_integrable _ _

variables [normed_space ℂ E] [complete_space E] [borel_space E] [second_countable_topology E]

/-- Definition for $\int_{|w-c|=R} f(w)\,dw$. -/
def circle_integral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
∫ (θ : ℝ) in 0..2 * π, deriv (circle_map c R) θ • f (circle_map c R θ)

notation `∮` binders ` in ` `C(` c `, ` R `)` `, ` r:(scoped:60 f, circle_integral f c R) := r

namespace circle_integral

@[simp] lemma integral_radius_zero (f : ℂ → E) (c : ℂ) : ∮ z in C(c, 0), f z = 0 :=
by simp [circle_integral]

lemma integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬circle_integrable f c R) :
  ∮ z in C(c, R), f z = 0 :=
begin
  rcases eq_or_ne R 0 with rfl|h0, { simp },
  refine interval_integral.integral_undef _, contrapose! hf,
  simp only [circle_integrable, deriv_circle_map, interval_integrable_iff] at *,
  refine (hf.norm.const_mul (|R|⁻¹)).mono' _ _,
  { have H : ∀ {θ}, circle_map 0 R θ * I ≠ 0 := λ θ, by simp [h0, I_ne_zero],
    simpa only [inv_smul_smul₀ H]
      using (((continuous_circle_map 0 R).ae_measurable _).mul_const I).inv.smul hf.ae_measurable },
  { simp [norm_smul, h0] },
end

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

/-- If `w : ℂ` is a point strictly inside the circle `metric.sphere c R` and `n ≠ -1` is an integer
number, then the integral of `(z - w) ^ n` over the circle equals zero. -/
lemma integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
  ∮ z in C(c, R), (z - w) ^ n = 0 :=
begin
  rcases em (w ∈ sphere c (|R|) ∧ n < -1) with ⟨hw, hn⟩|H,
  { rcases eq_or_ne R 0 with rfl|h0, { apply integral_radius_zero },
    apply integral_undef,
    rw [circle_integrable],
 },
  { suffices : ∀ {s} (z ∈ sphere c (|R|)),
      has_deriv_within_at (λ z, (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) s z,
      from integral_eq_zero_of_has_deriv_within_at' this,
    intros s z hz,
    convert ((has_deriv_at_zpow _ _ _).comp_has_deriv_within_at z
      ((has_deriv_within_at_id z s).sub_const w)).mul_const _,
    { have : (n + 1 : ℂ) ≠ 0,
        by rwa [ne, ← eq_neg_iff_add_eq_zero, ← int.cast_one, ← int.cast_neg, int.cast_inj],
      simp [mul_div_cancel_left _ this, ← div_eq_mul_inv] },
    { push_neg at H,
      refine imp_iff_not_or.1 (λ hzw, neg_le_iff_add_nonneg.1 _),
      exact H (sub_eq_zero.1 hzw ▸ hz) } }
end

end circle_integral
