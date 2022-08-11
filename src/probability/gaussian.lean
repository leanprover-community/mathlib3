import probability.density
import probability.moments
import analysis.special_functions.gaussian
import measure_theory.integral.set_to_l1
import analysis.normed_space.bounded_linear_maps
import topology.sequences

import algebra.order.ring
import data.complex.exponential
import topology.algebra.module.basic

import measure_theory.integral.integrable_on
import measure_theory.integral.bochner
import order.filter.indicator_function
import topology.metric_space.thickened_indicator



import measure_theory.covering.besicovitch_vector_space
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise
import measure_theory.covering.differentiation
import measure_theory.constructions.polish

import measure_theory.group.integration

#check real.exp_pos
#check measure_theory.integral_image_eq_integral_abs_det_fderiv_smul
#check measurable_set.univ
#check measure_theory.integral_image_eq_integral_abs_det_fderiv_smul
#check real.coe_to_nnreal
---#check probability_theory.moment,

/-
We would like to define the Gaussian measure on ℝ.
There are two ways of doing this.

(1). Given `E` a topological vector space equipped with the measure `μ`, we say `f : E → ℝ` is the
  standard Gaussian random variable with respect to `μ` if
  ```
    μ.with_density f = (volume : measure ℝ).with_density (λ x, √(2π)⁻¹ exp (-x² / 2)).
  ```
  Then, we say `μ` is a Gaussian measure if for all `l : E →L[ℝ] ℝ`, there exists some `m s : ℝ`
  such that `l = sf + m` where `f` is the standard Gaussian.

(2). Define the Gaussian measure on ℝ directly by saying `μ : measure ℝ` is a Gaussian measure
  if there exists `m s : ℝ` such that
  ```
    μ = if s ≠ 0 then (volume : measure ℝ).with_density
      (λ x, √(2πs²)⁻¹ exp (-(x - m)² / 2s²)) else δ(m)
  ```
  Then, we say a measure `μ` on the topological vector space `E` is Gaussian if for all
  `l : E →L[ℝ] ℝ`, `μ.map l` is a Gaussian measure on `ℝ`.

The first definition has the advantage of not having a if then else definition while it is
easier to work with the second definition as we have the density readily. We will use the
second definition.
-/

open_locale nnreal ennreal probability_theory measure_theory real

namespace measure_theory

open real

noncomputable def gaussian_density (m s : ℝ) : ℝ → ℝ≥0∞ :=
λ x, ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)

/-- We say a real measure is Gaussian if there exists some `m s : ℝ` such that the Radon-Nikodym
derivative of `μ` with respect to the Lebesgue integral is the Gaussian density with mean `m` and
standard deviation `s`. -/
def measure.real_gaussian (μ : measure ℝ) (m s : ℝ) : Prop :=
if s ≠ 0 then μ = volume.with_density (gaussian_density m s) else μ = measure.dirac m

open probability_theory measure

variables {μ : measure ℝ} {m s : ℝ}


lemma mulone_eq (g : ℝ → ℝ) (f : ℝ → ℝ): ∫ (x : ℝ) in set.univ, g (f x)
= ∫ (x : ℝ) in set.univ, 1 • g (f x) :=
begin
simp,
end





lemma onenng : 0 ≤ 1 := zero_le 1

lemma detid_eq_one : |(continuous_linear_map.id ℝ ℝ).det| = 1 :=
begin
have h_deteq : (continuous_linear_map.id ℝ ℝ).det = linear_map.det (linear_map.id),
  refl,
rw h_deteq,
simp,
end

lemma integ_smul_eq_mul (f : ℝ → ℝ) (g : ℝ → ℝ): ∫ (x : ℝ) in set.univ, 1 • g (f x)
 = ∫ (x : ℝ) in set.univ, |(continuous_linear_map.id ℝ ℝ).det| • g (f x) :=
begin
rw detid_eq_one,
simp,
end

-- change of variables
lemma change_of_vr_gaussian /-(μ : measure ℝ)-/:
   ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) = ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)):=
begin
    let g : ℝ → ℝ := λ (x:ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
    let f : ℝ → ℝ := λ (x:ℝ), x-m,
    have h_set_eq : set.univ = f '' set.univ,
      {ext e,
      split,
      {intro h1,
      use (e+m),
      split,
      simp,
      simp_rw [f],
      simp},
      {intro h2,
      simp}},

    have h_integ_eq : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2))
     = ∫ (x : ℝ) in set.univ, g (x-m) ,
      {simp_rw [g],
        simp},

    rw h_integ_eq,

    have h_integ_eq2 : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))
     = ∫ (x : ℝ) in set.univ, g x ,
      {simp_rw [g],
        simp},

    rw h_integ_eq2,
    nth_rewrite 1 [h_set_eq],

    have h_comp_eq : ∀ (x:ℝ), g (x-m) = g (f x),
      {intro x,
      simp},

    simp_rw [h_comp_eq],
    let f_deriv : ℝ →L[ℝ] ℝ := continuous_linear_map.id ℝ ℝ,
    let f': ℝ → (ℝ →L[ℝ] ℝ) := λ x, continuous_linear_map.id ℝ ℝ,

    rw mulone_eq g f,
    rw integ_smul_eq_mul f g,

    have h_use_f'_tosubst : ∫ (x : ℝ) in set.univ, |(continuous_linear_map.id ℝ ℝ).det| • g (f x)
     = ∫ (x : ℝ) in set.univ, |(f' x).det| • g (f x),
     {refl},

    rw h_use_f'_tosubst,

    have hf : set.inj_on f set.univ,
      refine set.injective_iff_inj_on_univ.mp _,
      unfold function.injective,
      intros a1 a2,
      simp_rw[f],
      simp,

    have hf' : ∀ (x : ℝ), x ∈ set.univ → has_fderiv_within_at f (f' x) set.univ x,
      {intros x hx,
      refine has_fderiv_within_at.sub_const _ m,
      exact has_fderiv_within_at_id x set.univ},
      {rw ← integral_image_eq_integral_abs_det_fderiv_smul ℙ measurable_set.univ hf' hf g},

end


-- 0 < s^2
lemma s_sq_pos (s : ℝ) (hs : s ≠ 0): 0 < s^2 :=
begin
  exact (sq_pos_iff s).mpr hs,
end

-- 0 < 2*s^2
lemma s_sq_pos_2 (s : ℝ) (hs : s ≠ 0): 0 < 2*s^2 :=
begin
  simp,
  exact s_sq_pos s hs,
end

-- nonegative x with sqrt equals to 0 is equal to zero
lemma pos_sqrt_zero_eq_zero : ∀ (x:ℝ), x ≥ 0 → sqrt x = 0 → x = 0 :=
begin
  intros x hx h,
  rw ← sq_sqrt hx,
  simp,
  exact h,
end

-- 0 < 2*π*s^2
lemma s_sq_pos_2_pi (s : ℝ) (hs : s ≠ 0): 0 < 2*π*s^2 :=
begin
  ring_nf,
  simp [s_sq_pos_2 s hs],
  exact pi_pos,
end

-- commutativity inside the integral
lemma comm_in_integ (f : ℝ → ℝ) (c : ℝ):
    ∫ x : ℝ, (f x) * c ∂ℙ = ∫ x : ℝ, c * f x :=
begin
simp_rw [mul_comm],
end

-- to remove the certain bracket of (2 • π) • s ^ 2
--change it into 2 • π • s ^ 2
lemma smul_no_bracket (s : ℝ) (hs : s ≠ 0): (2 • π) • s ^ 2 = 2 • π • s ^ 2 :=
begin
simp,
exact mul_assoc 2 π (s^2),
end

lemma change_onemul_to_smul (f:ℝ → ℝ): ∫ (x : ℝ), f x * (sqrt (2 * π * s ^ 2))⁻¹
 = ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹:=
begin
simp_rw[← smul_eq_mul],
end


lemma like_gaussian_eval (s:ℝ) (hs : s≠0): ∫ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)) = sqrt (2 * π * s ^ 2) :=
begin
  have h : s * s⁻¹ = 1,
    finish,
  have h_inveq : (2*s^2)⁻¹ = (s ^ 2)⁻¹ * 2⁻¹,
    ring_nf,
    simp,
    ring,
  rw ← h_inveq,
  simp_rw [← neg_mul],
  rw integral_gaussian (2*s^2)⁻¹,
  ring_nf,
  simp,
end

lemma sqrt_not_zero (s:ℝ) (hs : s≠0): sqrt (2*π*s^2) ≠ 0:=
begin
  have h_conpos : ∀ (x:ℝ), x ≥ 0 → x ≠ 0 → sqrt x ≠ 0 ,
    intros x hx h,
    exact mt (pos_sqrt_zero_eq_zero x hx) h,

  apply h_conpos,
  exact le_of_lt (s_sq_pos_2_pi s hs),
  exact ne_of_gt (s_sq_pos_2_pi s hs),

end

lemma mul_inv_eq_one (a:ℝ) (ha: a≠0): a * a⁻¹ = 1:=
begin
finish,
end

---important result below
lemma is_probability_measure_real_gaussian (hμ : μ.real_gaussian m s) :
  is_probability_measure μ :=
begin
  rw real_gaussian at hμ,
  split_ifs at hμ,
 {
    unfold gaussian_density at hμ,
    refine {measure_univ := _},
    rw hμ,
    simp only [mul_inv_rev, neg_mul, with_density_apply, measurable_set.univ, restrict_univ],
    rw ← measure_theory.of_real_integral_eq_lintegral_of_real,

    {rw change_of_vr_gaussian,
     let f : ℝ → ℝ := λ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
     have h_changeform : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))
    = ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * f x,
      refl,
    rw h_changeform,
    rw ← comm_in_integ f (sqrt (2 * π * s ^ 2))⁻¹,
    rw change_onemul_to_smul f,
    have h_integral_smul_const_special : ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹ ∂ℙ
    = (∫ (x : ℝ), f x ∂ℙ) • (sqrt (2 * π * s ^ 2))⁻¹,
      {
        exact integral_smul_const f (sqrt (2 * π * s ^ 2))⁻¹,
      },
    rw h_integral_smul_const_special,
    simp_rw [f],
    rw like_gaussian_eval s h,
    simp [h],
    have h_sqrt_not_zero : sqrt (2*π*s^2) ≠ 0,
      {exact sqrt_not_zero s h},

    rw mul_inv_eq_one (sqrt (2*π*s^2)) h_sqrt_not_zero,
    simp,
    ---exact μ,
    },
    {
      rw integrable, fconstructor,
      {
        measurability,
      },
      {
        refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)))).mp
  _,
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ (sqrt (2 * π * s ^ 2))⁻¹,

        have neg_h_inveq : -(2*s^2)⁻¹ = -(s ^ 2)⁻¹ * 2⁻¹,
        { simp [mul_comm] },

        have hb : 0 < (2*s^2)⁻¹ := inv_pos.mpr (s_sq_pos_2 s h),

        have h_gaussexp : integrable (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * a ^ 2)) ℙ,
          rw ← neg_h_inveq,
          exact integrable_exp_neg_mul_sq hb,

        have h_eqfunc : (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * (a - m)^ 2)) = (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * (a - m) ^ 2)))  ,
          ext x,
          simp,

        rw ← h_eqfunc,
        exact measure_theory.integrable.comp_sub_right h_gaussexp m,
      }
    },
    {refine filter.eventually_of_forall _,

      have h_exppos : 0 < (2 * s ^ 2) * π,
        exact mul_pos (s_sq_pos_2 s h) pi_pos,

      have h_sqrt_pos :  0 < sqrt(2 * s ^ 2 * π),
        exact sqrt_pos.mpr h_exppos,

      have  h_const_pos :  0 < (sqrt(2 * s ^ 2 * π))⁻¹,
        exact inv_pos.mpr h_sqrt_pos,
      have h_mulpi_eq : 2 * s ^ 2 * π = 2 * π * s ^ 2,
        ring,

      rw h_mulpi_eq at h_const_pos,
      intro x,
      have h_compexp_pos : 0 < exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)),
        exact real.exp_pos (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)),
      simp,
      rw  le_iff_lt_or_eq,
      left,
      exact mul_pos h_const_pos h_compexp_pos,
    }
  },

   -- the lemma `integral_gaussian` is useful!
  { refine {measure_univ := _},
  rw hμ,
  simp
  },
end





lemma gaussian_density_ennreal (hs : s ≠ 0) : ∀ (x:ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)≥ 0 :=
begin
  intro x,
  simp,
  have h_exp_pos :  exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) > 0 := (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)).exp_pos,
  have h_invsqrt_pos : (sqrt (2 * π * s ^ 2))⁻¹ > 0,
    {simp,
    exact s_sq_pos_2_pi s hs},
  have h_prod_of_poses_pos : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) > 0 := mul_pos h_invsqrt_pos h_exp_pos,
  exact le_of_lt h_prod_of_poses_pos,
end

lemma eq_integ_in_univ : ∫ (x : ℝ), id x ∂μ =  ∫ (x : ℝ) in set.univ, id x ∂μ :=
begin
  simp,
end

lemma univ_eq_nneg_union_neg : set.univ = {x:ℝ|0≤x} ∪ {x:ℝ|x<0}:=
begin
ext x,
split,
{intro hx,
simp,
exact le_or_lt 0 x},
{intro hx,
simp},
end


---define the equivalent gaussian density mapping ℝ → ℝ≥0 instead
---of ℝ → ℝ≥0∞;
---we do this for later using integral_with_density_eq_integral_smul
noncomputable def gaussian_density_to_nnreal (m s : ℝ) : ℝ → ℝ≥0 :=
λ x, ennreal.to_nnreal (ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2))

lemma eqform_of_gauden_to_nnreal : ∀ (x:ℝ), gaussian_density m s x = gaussian_density_to_nnreal m s x:=
---λ x, ennreal.to_nnreal (ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)):=
begin
  unfold gaussian_density,
  unfold gaussian_density_to_nnreal,
  simp,
end

lemma eqform_of_gauden_mea : measurable (gaussian_density_to_nnreal m s):=
begin
  unfold gaussian_density_to_nnreal,
  measurability,
end

---lemma eqform_gauden_to_real (hs : s ≠ 0): :=
/-
lemma ennreal_no_act_on_posfunc (f : ℝ → ℝ) : f ≥ 0 →
∀ (x:ℝ), f x = (λ x, ennreal.of_real (f x) x:=
begin-/



lemma simple_thing (x:ℝ) (hx : x≥0): x = ((ennreal.of_real x).to_nnreal):=
begin
  unfold ennreal.of_real,
  simp,
  by_cases (x=0),
  rw h,
  simp,
  have hx2 : x>0,
    exact (ne.symm h).lt_of_le hx,
  have h : max x 0 = x,
    {simp,
    exact hx},
  exact eq.symm h,
end

lemma not_that_simple_thing (hs : s ≠ 0): ∀ (x:ℝ),
  (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x
  = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal • x :=
begin
  intro x,
  rw smul_eq_mul,
  have h_smul_eq_mul : (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal • x
   = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal * x,
   {exact rfl},

  rw h_smul_eq_mul,

  have h_exprepos : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) ≥ 0,
    {exact gaussian_density_ennreal hs x},

  have h_no_smul_eq : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)
    = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal,
    {exact simple_thing ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) h_exprepos},

  by_cases (x=0),
  rw h,
  simp,
  have h_nonneg_smul_nneg_eq : ∀ (a b : ℝ), a = b ↔ a * x = b * x,
    {intros a b,
    split,
    intro h1,
    simp,
    left,
    exact h1,
    intro h2,
    simp [h] at h2,
    exact h2},
  rw ← mul_assoc (sqrt (2 * π * s ^ 2))⁻¹  (exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) x,
  rw ← h_nonneg_smul_nneg_eq ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal,
  exact h_no_smul_eq,
end

lemma simp_inv (a b : ℝ) (hb : b ≠ 0): a = a * b * b⁻¹ :=
begin
  have h_mulassoc : a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc a b b⁻¹,
  rw h_mulassoc,
  simp [hb],
end

lemma twos_neq_zero (hs : s ≠ 0) : sqrt (2 * s^2) ≠ 0 :=
begin
  have h_conpos : ∀ (x:ℝ), x ≥ 0 → x ≠ 0 → sqrt x ≠ 0 ,
    intros x hx h,
    exact mt (pos_sqrt_zero_eq_zero x hx) h,

  apply h_conpos,
  simp,
  exact sq_nonneg s,
  simp,
  exact hs,
end

lemma simplify_sqrt_and_square_in_exp (hs : s≠0) : ∀ (x:ℝ),
exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) =
exp (-((sqrt (2 * s ^ 2))⁻¹ * (x - m)) ^ 2):=
begin
  intro x,
  simp,
  have h_squarenn : 0 ≤ s^2 := sq_nonneg s,

  have h1 : sqrt (s ^ 2) ^ 2 = s ^ 2,
    {simp [h_squarenn]},

  have h2 : (sqrt 2)⁻¹ ^ 2 = 2⁻¹,
    {
      simp,
    },

  have h3 : ((sqrt (s ^ 2))⁻¹ * (sqrt 2)⁻¹ * (x - m)) ^ 2 =
  ((sqrt (s ^ 2))⁻¹ ^ 2) * ((sqrt 2)⁻¹ ^ 2) * (x - m) ^ 2,
    {ring_nf},

  rw h3,

  have h_eliminate_sqrt_s: (sqrt (s ^ 2))⁻¹ ^ 2 = (s^2)⁻¹,
    {
      simp [h1],
    },
  simp [h_eliminate_sqrt_s, h2],

end


lemma simplify_sqrt_and_square_out_exp (hs : s≠0) : ∀ (x:ℝ),
(sqrt (2 * s ^ 2) * ((sqrt (2 * s ^ 2))⁻¹ * (x - m)) + m) = x :=
begin
  intro x,
  rw ← mul_assoc (sqrt (2 * s ^ 2)) (sqrt (2 * s ^ 2))⁻¹  (x - m),
  have h1 : sqrt (2 * s ^ 2) ≠ 0 := twos_neq_zero hs,
  have h2 : ∀ (x:ℝ), x≠0 → x * x⁻¹ = 1,
    {intros x hx,
    finish},
  have h2 : (sqrt (2 * s ^ 2)) * (sqrt (2 * s ^ 2))⁻¹ = 1 := h2 (sqrt (2 * s ^ 2)) h1,
  rw h2,
  simp,

end




lemma simplify_complicated1 (hs : s≠0): ∀ (x:ℝ), /-(sqrt (2 * s ^ 2))⁻¹ *--/ (exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) * x)
= (exp (-((sqrt (2 * s ^ 2))⁻¹ * (x - m)) ^ 2) * (sqrt (2 * s ^ 2) * ((sqrt (2 * s ^ 2))⁻¹ * (x - m)) + m)) :=
begin
  intro x,
  ---simp,
  simp_rw [← simplify_sqrt_and_square_in_exp hs],
  simp_rw [simplify_sqrt_and_square_out_exp hs],

end

lemma simplify_complicated2 (hs : s≠0): ∀ (x:ℝ),
(sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2) =
(sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2):=
begin
  intro x,
  simp,
end



---lemma set_eq (hs : s≠0): set.univ = λ (x:ℝ), ((sqrt (2 * s ^ 2))⁻¹) * (x-m):=
lemma change_of_vr_momentone_gaussian (hs: s≠0):
∫ (x : ℝ), exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x * (sqrt (2*s^2))⁻¹
 = ∫ (x : ℝ), ((sqrt (2 * s ^ 2))* x + m) * exp (- x ^ 2) :=
begin
  let g : ℝ → ℝ := λ (x:ℝ), exp (- x ^ 2) * ((sqrt (2 * s ^ 2))*x + m),
  let f : ℝ → ℝ := λ (x:ℝ), (sqrt (2 * s ^ 2))⁻¹ * (x-m),

  have h_set_eq : set.univ = f '' set.univ,
    {ext e,
    split,
    {intro h1,
    use (sqrt (2 * s ^ 2))*e+m,
    split,
    {simp},
    {simp_rw [f],
    ---simp,
    ring_nf,
    rw ← simp_inv e (sqrt (2 * s ^ 2)) (twos_neq_zero hs),
    },
    },
    {intro h2,
    simp}},
  simp,
  have h_integ_eq_form1 : ∫ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) * x * ((sqrt (s ^ 2))⁻¹ * (sqrt 2)⁻¹)
   = ∫ (x : ℝ) in set.univ, g ( (sqrt (2 * s ^ 2))⁻¹ * (x-m)) * ((sqrt (s ^ 2))⁻¹ * (sqrt 2)⁻¹),
    {
      simp_rw [g],
      simp_rw [← simplify_complicated1 hs],
      simp,
    },
  rw h_integ_eq_form1,
  have h_integ_eq_form2 : ∫ (x : ℝ), (sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2)
   = ∫ (x : ℝ), g x,
   {
    simp_rw [g],
    simp,
    sorry
   }
  sorry
--(sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2)
end

--lemma eqform_of_gauden_to_nnreal_mea : measurable
lemma moment_one_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  μ[id] = m :=
begin
  have h_is_prob_mea : is_probability_measure μ,
  {exact is_probability_measure_real_gaussian hμ},
  rw real_gaussian at hμ,
  split_ifs at hμ,
  rw hμ,
  have h_lambdaform : gaussian_density m s = λ x, (gaussian_density_to_nnreal m s) x,
    {ext x,
    unfold gaussian_density,
    unfold gaussian_density_to_nnreal,
    simp},
  rw h_lambdaform,
  rw integral_with_density_eq_integral_smul eqform_of_gauden_mea id,
  unfold gaussian_density_to_nnreal,


  ---simp [gaussian_density_ennreal, hs],
  have h_eliminate_ennreal_nnreal :
  ∫ (a : ℝ), (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2))).to_nnreal • a
  = ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a,
  {
    simp_rw [← not_that_simple_thing hs],

  },
  simp_rw [id],

  rw h_eliminate_ennreal_nnreal,
  --dsimp at *,

  let f : ℝ → ℝ := λ (a : ℝ), exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a,
  have h_changeform : ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a =
  ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * f a,
  {
    simp_rw[f]
  },
  rw h_changeform,
  rw ← comm_in_integ f (sqrt (2 * π * s ^ 2))⁻¹,
  rw change_onemul_to_smul f,
  have h_integral_smul_const_special : ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹ ∂ℙ
    = (∫ (x : ℝ), f x ∂ℙ) • (sqrt (2 * π * s ^ 2))⁻¹,
      {
        exact integral_smul_const f (sqrt (2 * π * s ^ 2))⁻¹,
      },
  rw h_integral_smul_const_special,
  simp_rw[f],



end

-- easy direction
lemma absolutely_continuous_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  μ ≪ volume :=
begin
  sorry
end

-- harder
lemma real_gaussian_absolutely_continuous (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  volume ≪ μ :=
begin
  -- Hint: first show/find in mathlib that for positive `f`, `∫ x in s, f x ∂μ = 0 ↔ μ s = 0`
  -- Do it on paper first!
  sorry
end

section gaussian_rv

/- ### Transformation of Gaussian random variables -/

variables {α : Type*} [measure_space α]

/-- A real-valued random variable is a Gaussian if its push-forward measure is a Gaussian measure
on ℝ. -/
def gaussian_rv (f : α → ℝ) (m s : ℝ) : Prop := (volume.map f).real_gaussian m s

def std_gaussian_rv (f : α → ℝ) : Prop := gaussian_rv f 0 1

variables {f g : α → ℝ} {m₁ s₁ m₂ s₂ : ℝ}

lemma std_gaussian_rv_add_const (hf : std_gaussian_rv f) (hfmeas : measurable f) (m : ℝ) :
  gaussian_rv (f + λ x, m) m 1 :=
begin
  unfold std_gaussian_rv at hf,
  unfold gaussian_rv at *,
  unfold real_gaussian at *,
  simp at *,
  ---unfold with_density at *,

  ---unfold map at *,

  have h_ae_m_one : ae_measurable (λ (a : α), 1) ℙ,
    simp,
  have h_ae_m_const : ae_measurable (λ (a : α), m) ℙ,
    exact ae_measurable_const,
  have h_eq_ae_m : ae_measurable f ℙ ↔ ae_measurable (f+λ (a : α), m) ℙ,
    split,
    intro h_eq_ae_m1,
    exact ae_measurable.add' h_eq_ae_m1 h_ae_m_const,
    intro h_eq_ae_m2,
    exact measurable.ae_measurable hfmeas,
  have h_zeroeqno : f = f + λ (a : α), 0,
    ext x,
    simp,
  rw h_zeroeqno at hf,

  sorry,


end

lemma std_gaussian_rv_const_smul (hf : std_gaussian_rv f) (hfmeas : measurable f) (s : ℝ) :
  gaussian_rv (s • f) 0 s :=
begin
  sorry
end
--test --
-- Hard!
lemma gaussian_rv_add (hf : gaussian_rv f m₁ s₁) (hg : gaussian_rv g m₂ s₂)
  (hfmeas : measurable f) (hgmeas : measurable g) (hfg : indep_fun f g) :
  gaussian_rv (f + g) (m₁ + m₂) (sqrt (s₁^2 + s₂^2)) :=
begin
  sorry
end

lemma mgf_gaussian_rv  (hf : gaussian_rv f m s) (hfmeas : measurable f) (t : ℝ) :
  mgf f volume t = exp (m * t + s^2 * t^2 / 2) :=
begin
  sorry
end

end gaussian_rv

section tvs

/- ### Gaussian measure on TVS -/

variables {E : Type*} [measurable_space E]
  [topological_space E] [add_comm_monoid E] [module ℝ E]

/-- A measure `ν` on a topological vector space `E` is said to be a Gaussian measure if for all
continuous linear functionals `l` of `E`, the push-forward measure of `l` along `ν` is a Gaussian
measure on ℝ with mean 0. -/
def gaussian (ν : measure E) : Prop :=
∀ l : E →L[ℝ] ℝ, ∃ s, (ν.map l).real_gaussian 0 s

end tvs

end measure_theory
