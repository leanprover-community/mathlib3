import measure_theory.integral.interval_integral

/-!
-/

variables {E : Type*} [measurable_space E] [normed_group E]

noncomputable theory

open_locale real nnreal interval
open complex measure_theory topological_space metric

def circle_map (z : ℂ) (R : ℝ≥0) : ℝ → ℂ := λ θ, z + R * exp (θ * I)

lemma circle_map_mem_sphere (z : ℂ) (R : ℝ≥0) (θ : ℝ) : circle_map z R θ ∈ sphere z R :=
by simp [circle_map]

@[simp] lemma abs_circle_map_zero (R : ℝ≥0) (θ : ℝ) : abs (circle_map 0 R θ) = R :=
by simpa only [complex.norm_eq_abs, mem_sphere_zero_iff_norm] using circle_map_mem_sphere 0 R θ

lemma circle_map_mem_closed_ball (z : ℂ) (R : ℝ≥0) (θ : ℝ) :
  circle_map z R θ ∈ closed_ball z R :=
sphere_subset_closed_ball (circle_map_mem_sphere z R θ)

lemma has_deriv_at_circle_map (z : ℂ) (R : ℝ≥0) (θ : ℝ) :
  has_deriv_at (circle_map z R) (circle_map 0 R θ * I) θ :=
by simpa only [mul_assoc, one_mul, of_real_clm_apply, circle_map, of_real_one, zero_add]
 using ((of_real_clm.has_deriv_at.mul_const I).cexp_real.const_mul (R : ℂ)).const_add z

lemma differentiable_circle_map (z : ℂ) (R : ℝ≥0) :
  differentiable ℝ (circle_map z R) :=
λ θ, (has_deriv_at_circle_map z R θ).differentiable_at

lemma continuous_circle_map (z : ℂ) (R : ℝ≥0) : continuous (circle_map z R) :=
(differentiable_circle_map z R).continuous

def circle_integrable (f : ℂ → E) (z : ℂ) (R : ℝ≥0) : Prop :=
interval_integrable (λ θ : ℝ, f (circle_map z R θ)) volume 0 (2 * π)

@[simp] lemma circle_integrable_const (c : E) (z : ℂ) (R : ℝ≥0) :
  circle_integrable (λ _, c) z R :=
interval_integrable_const

namespace circle_integrable

variables {f g : ℂ → E} {z : ℂ} {R : ℝ≥0}

lemma add [borel_space E] [second_countable_topology E]
  (hf : circle_integrable f z R) (hg : circle_integrable g z R) :
  circle_integrable (f + g) z R :=
hf.add hg

lemma neg [borel_space E] (hf : circle_integrable f z R) : circle_integrable (-f) z R := hf.neg

/-- The function we actually integrate over `[0, 2π]` is integrable. -/
lemma out [borel_space E] [normed_space ℂ E] [second_countable_topology E]
  (hf : circle_integrable f z R) :
  interval_integrable (λ θ : ℝ, (circle_map 0 R θ * I) • f (circle_map z R θ)) volume 0 (2 * π) :=
begin
  simp only [circle_integrable, interval_integrable_iff] at *,
  refine (hf.norm.const_mul R).mono' _ _,
  { exact (((continuous_circle_map _ _).ae_measurable _).mul_const I).smul hf.ae_measurable },
  { simp [norm_smul] }
end

end circle_integrable

lemma continuous_on.circle_integrable [borel_space E] {f : ℂ → E} {z : ℂ} {R : ℝ≥0}
  (hf : continuous_on f (sphere z R)) :
  circle_integrable f z R :=
(hf.comp_continuous (continuous_circle_map _ _)
  (circle_map_mem_sphere _ _)).interval_integrable _ _

variables [normed_space ℂ E] [complete_space E] [borel_space E] [second_countable_topology E]

/-- Definition for $\int_{|w-z|=R} f(w)\,dw$. -/
def circle_integral (f : ℂ → E) (z : ℂ) (R : ℝ) : E :=
∫ (θ : ℝ) in 0..2 * π, (R * exp (θ * I) * I : ℂ) • f (z + R * exp (θ * I))

notation `∮` binders ` in ` `C(` z `,` R `)` `, ` r:(scoped:60 f, circle_integral f z R) := r

@[simp] lemma circle_integral.integral_smul_const
