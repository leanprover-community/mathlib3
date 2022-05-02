/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import analysis.complex.cauchy_integral
import analysis.analytic.basic
import analysis.calculus.parametric_interval_integral
import data.complex.basic
import measure_theory.integral.circle_integral
/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic facts
about these functions.

These functions are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/

open topological_space set measure_theory interval_integral metric filter function complex
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u v

variables {E : Type u} [normed_group E] [normed_space ℂ E]

namespace complex

/--Given a function `f : ℂ → E`, this gives the function  $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x`
runs over a circle of radius `R` around `z`. If `f` is differntiable and `w` is in the interior of
the ball, then the integral from `0` to `2 * π` of this gives the value `f(w)` -/
def circle_integral_transform (R : ℝ) (z w: ℂ) (f : ℂ → E) : (ℝ → E) := λ θ,
 (2 * π * I : ℂ)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f  (circle_map z R θ)

/--The derivative of `circle_integral_transform` w.r.t `w` -/
def circle_integral_transform_deriv (R : ℝ) (z w : ℂ) (f : ℂ → E) : (ℝ → E) := λ θ,
  (2 * π * I : ℂ)⁻¹ • deriv (circle_map z R) θ •
  (((circle_map z R θ) - w)^(2))⁻¹ • f  (circle_map z R θ)

/--Cauchy integral form of a function around a disk of radius `R` around `z`-/
def circle_integral_form [complete_space E] (R : ℝ) (z : ℂ) (f : ℂ → E) : (ℂ → E) :=
  λ w, (2 * π * I : ℂ)⁻¹ • (∮ z in C(z, R), (z - w)⁻¹ • f z)

lemma circle_intgral_form_eq_int [complete_space E] (R : ℝ) (z : ℂ) (f : ℂ → E) :
  circle_integral_form R z f =  λ w,
 ∫ (θ : ℝ) in 0..2 * π, (circle_integral_transform R z w f ) θ :=
begin
  simp_rw [circle_integral_form,circle_integral_transform, circle_integral,
  interval_integral.integral_smul],
end

lemma circle_integral_transform_deriv_eq (R : ℝ) (z w : ℂ) (f : ℂ → E) :
  circle_integral_transform_deriv  R z w f = (λ θ,
  ((circle_map z R θ) - w)⁻¹ • (circle_integral_transform R z w f θ)) :=
begin
  ext,
  simp_rw [circle_integral_transform_deriv, circle_integral_transform, pow_two, ←mul_smul,
   ←mul_assoc],
  ring_nf,
  congr',
  rw [pow_two, mul_inv₀],
end

lemma circle_integral_transform_circle_int [complete_space E] (R : ℝ) (z w : ℂ) (f : ℂ → E) :
  ∫ (θ : ℝ) in 0..2 * π, circle_integral_transform R z w f θ =
 (2 * π * I : ℂ)⁻¹ •  ∮ z in C(z, R), (z - w)⁻¹ • f z :=
begin
  simp_rw [circle_integral_transform,circle_integral,deriv_circle_map, circle_map],
  simp only [real_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, one_div,
  interval_integral.integral_smul, zero_add],
end

lemma circle_integral_transform_cont_on_ICC (R : ℝ) (hR : 0 < R)  (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R))
  (hw : w ∈ ball z R) :
  continuous_on (circle_integral_transform R z w f) [0, 2 * π] :=
begin
  rw circle_integral_transform,
  apply_rules [continuous_on.smul, continuous_const.continuous_on],
  simp_rw deriv_circle_map,
  have := (continuous_circle_map 0 R).continuous_on,
  apply_rules [continuous_on.mul, this, continuous_const.continuous_on],
  apply circle_map_inv_continuous_on R hR z w hw,
  apply continuous_on.comp hf (continuous_circle_map z R).continuous_on,
  refine (λ _ _,  (circle_map_mem_sphere _ hR.le) _),
end

lemma circle_integral_transform_deriv_cont_on_ICC (R : ℝ) (hR : 0 < R) (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)) (hw : w ∈ ball z R) :
  continuous_on (circle_integral_transform_deriv R z w f) [0, 2 * π] :=
begin
  rw circle_integral_transform_deriv_eq,
  refine (circle_map_inv_continuous_on R hR z w hw).smul
  (circle_integral_transform_cont_on_ICC R hR f z w hf hw),
end

lemma circle_integral_transform_cont_on (R : ℝ) (hR : 0 < R) (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)) (hw : w ∈ ball z R):
  continuous_on (circle_integral_transform R z w f) (Ι 0 (2 * π)) :=
begin
 apply (circle_integral_transform_cont_on_ICC R hR f z w hf hw).mono,
 simp_rw [interval_oc_of_le (real.two_pi_pos.le), interval_of_le (real.two_pi_pos.le),
 Ioc_subset_Icc_self],
end

/--A useful bound for circle integrals (with complex codomain)-/
def circle_integral_bounding_function (R : ℝ) (z : ℂ) : (ℂ × ℝ → ℂ) :=
  λ w, circle_integral_transform_deriv R z w.1 (λ x, 1) w.2

lemma circle_int_funct_cont_on_prod  (R r : ℝ) (hR : 0 < R) (hr : r < R) (z : ℂ) :
 continuous_on (λ (w : ℂ × ℝ), ((circle_map z R w.snd - w.fst)⁻¹)^2)
  (((closed_ball z r) ×ˢ (interval 0 (2 * π))) : set (ℂ × ℝ)) :=
begin
  simp_rw ←one_div,
  apply_rules [continuous_on.pow, continuous_on.div, continuous_const.continuous_on,
  continuous_on.sub (continuous_on.comp (continuous_circle_map z R).continuous_on
  continuous_on_snd (λ _, and.right)) (continuous_on.comp  continuous_on_id continuous_on_fst
  (λ _, and.left))],
  simp only [mem_prod, mem_closed_ball, ne.def, and_imp, prod.forall],
  intros a b ha hb,
  apply (circle_map_ne_on_ball _ hR),
  simp only [mem_ball],
  linarith,
end

lemma circle_integral_bounding_function_continuous_on (R r : ℝ) (hR : 0 < R) (hr : r < R) (z : ℂ) :
  continuous_on (complex.abs ∘ (circle_integral_bounding_function R z ))
  (((closed_ball z r) ×ˢ (interval 0 (2 * π))) : set (ℂ × ℝ)) :=
begin
  have c3 : continuous_on (circle_integral_bounding_function R z) (closed_ball z r ×ˢ [0, 2 * π]),
  by {simp_rw [circle_integral_bounding_function],
  apply continuous_on.smul continuous_const.continuous_on ,
  apply_rules [continuous_on.smul, continuous_const.continuous_on],
  simp only [deriv_circle_map],
  have c1 := (continuous_circle_map 0 R).continuous_on ,
  apply_rules [continuous_on.mul, continuous_on.comp c1 continuous_on_snd (λ _, and.right),
  continuous_const.continuous_on],
  simp_rw ←inv_pow₀,
  apply (circle_int_funct_cont_on_prod R r hR hr z),
  all_goals{apply_instance}},
  have C: maps_to (circle_integral_bounding_function R z) (closed_ball z r ×ˢ [0, 2 * π])
  (⊤ : set ℂ), by {simp [maps_to],},
  apply continuous_on.comp (continuous_abs.continuous_on) c3 C,
end

lemma circle_integral_bounding_function_bound (R r : ℝ) (hR: 0 < R) (hr : r < R) (hr' : 0 ≤  r)
  (z : ℂ) : ∃ (x :  ((closed_ball z r) ×ˢ (interval 0 (2 * π)) : set (ℂ × ℝ)) ),
  ∀ (y :  ((closed_ball z r) ×ˢ (interval 0 (2*π)) : set (ℂ × ℝ)) ),
  complex.abs (circle_integral_bounding_function R z y) ≤
  complex.abs(circle_integral_bounding_function R z x) :=
begin
  have cts := circle_integral_bounding_function_continuous_on R r hR hr z,
  have comp : is_compact (((closed_ball z r) ×ˢ (interval 0 (2*π))) : set (ℂ × ℝ)),
  by {apply_rules [is_compact.prod, proper_space.is_compact_closed_ball z r, is_compact_interval],},
  have none : (((closed_ball z r) ×ˢ (interval 0 (2*π))) : set (ℂ × ℝ)).nonempty ,
  by {apply nonempty.prod (nonempty_closed_ball.2 hr') (nonempty_interval)},
  have := is_compact.exists_forall_ge comp none cts,
  simp only [set_coe.forall, mem_prod, mem_closed_ball, subtype.coe_mk, and_imp, prod.forall,
  set_coe.exists, exists_prop, prod.exists, comp_app] at *,
  apply this,
end

lemma circle_integral_transform_deriv_cont_on (R : ℝ) (hR : 0 < R) (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)) (hw : w ∈ ball z R) :
  continuous_on (circle_integral_transform_deriv R z w f ) (Ι 0 (2*π)) :=
begin
 apply (circle_integral_transform_deriv_cont_on_ICC R hR f z w hf hw).mono,
 simp_rw [interval_oc_of_le (real.two_pi_pos.le), interval_of_le (real.two_pi_pos.le),
 Ioc_subset_Icc_self],
end

/--The derivative of a `circle_integral_transform` is bounded -/
lemma circle_integral_transform_deriv_bound (R r : ℝ)  (hR: 0 < R) (hr : r < R) (hr' : 0 ≤  r)
  (z : ℂ) (f : ℂ → ℂ) (x : ℂ) (hx : x ∈ ball z r) (hf : continuous_on f (sphere z R)) :
  ∃ (bound : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ ball x ε ⊆ ball z R ∧
  (∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε,
  ∥circle_integral_transform_deriv R z y f t∥ ≤  bound t) ∧ continuous_on bound [0, 2 * π] :=
 begin
  have HBB := ball_subset_ball hr.le,
  have h2R : 0 < 2 * R, by {linarith,},
  have fbb := circle_integral_bounding_function_bound R r hR hr hr' z,
  have ball := exists_ball_subset_ball hx,
  obtain ⟨ε', hε', H⟩ := ball,
  simp only [set_coe.forall, mem_prod, mem_closed_ball, subtype.coe_mk, and_imp, prod.forall,
  set_coe.exists, exists_prop, prod.exists] at fbb,
  obtain ⟨ a, b, hab⟩ := fbb,
  set V : ℝ → (ℂ → ℂ) := λ θ, λ w, circle_integral_transform_deriv R z w (λ x, 1) θ,
  set bound : ℝ → ℝ := λ r, (complex.abs (V b a)) * complex.abs (f(circle_map z R r)),
  refine ⟨bound, ε', _⟩,
  simp only [gt_iff_lt] at hε',
  simp only [hε', true_and, mem_ball, norm_eq_abs, (subset.trans H HBB), true_and],
  split,
  apply eventually_of_forall,
  intros y hy v hv,
  have hvv : v ∈ ball x ε', by {simp only [mem_ball, hv]},
  simp only [bound, circle_integral_bounding_function, circle_integral_transform_deriv,
  V, one_div, abs_of_real, abs_exp_of_real_mul_I, mem_ball,
  mul_one, algebra.id.smul_eq_mul, abs_I, nat.cast_bit0, real_smul, abs_mul, nsmul_eq_mul, abs_div,
  zero_lt_bit0, abs_inv, zero_lt_mul_left, nat.cast_one, abs_two, abs_pow,zero_lt_one] at *,
  have := mul_le_mul_of_nonneg_right (hab.2 v y (mem_ball.1 (H hvv)).le (Ioc_subset_Icc_self hy))
  (abs_nonneg (f(circle_map z R y))),
  simp_rw [deriv_circle_map, abs_mul, abs_circle_map_zero, abs_I, mul_one, ←mul_assoc] at *,
  apply this,
  simp_rw bound,
  have cabs : continuous_on abs ⊤, by {apply continuous_abs.continuous_on,},
  simp_rw ←abs_mul,
  apply_rules [cabs.comp,(continuous_const.continuous_on).mul, (continuous_on.comp hf),
  (continuous_circle_map z R).continuous_on],
  work_on_goal 2 {exact semi_normed_ring_top_monoid},
  all_goals {rw maps_to, intros x hx,},
  apply circle_map_mem_sphere _ hR.le,
  simp,
 end

end complex
