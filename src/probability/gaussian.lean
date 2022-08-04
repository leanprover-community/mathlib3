import probability.density
import probability.moments
import analysis.special_functions.gaussian
import measure_theory.group.integration

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
λ x, ennreal.of_real $ (sqrt (2 * π * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)

/-- We say a real measure is Gaussian if there exists some `m s : ℝ` such that the Radon-Nikodym
derivative of `μ` with respect to the Lebesgue integral is the Gaussian density with mean `m` and
standard deviation `s`. -/
def measure.real_gaussian (μ : measure ℝ) (m s : ℝ) : Prop :=
if s ≠ 0 then μ = volume.with_density (gaussian_density m s) else μ = measure.dirac m

open probability_theory measure

variables {μ : measure ℝ} {m s : ℝ}

lemma change_of_vr_gaussian:
   ennreal.of_real (∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2))) = ennreal.of_real (∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))):=
begin
sorry
end

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
    {

      --rw integral_smul_const _ (sqrt (2 * π * s ^ 2))⁻¹,
      sorry
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
        refine integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ (sqrt (2 * π * s ^ 2))⁻¹,
        have hbp1 : 0 < s^2,
          exact (sq_pos_iff s).mpr h,
        --have hbp2 : 0 < 2
        have hbp2 : 0 < 2*s^2,
          simp,
          exact hbp1,
        have h_inveq : -(2*s^2)⁻¹ = -(s ^ 2)⁻¹ * 2⁻¹,
          ring_nf,
          simp,
          ring,
        have hb : 0 < (2*s^2)⁻¹,
          exact inv_pos.mpr hbp2,
          ---rw ← h_inveq,


        have h_gaussexp : integrable (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * a ^ 2)) ℙ,
          rw ← h_inveq,
          ---rw h_minusmul (2*s^2)⁻¹ a,
          ---simp [integrable_exp_neg_mul_sq hb],
          exact integrable_exp_neg_mul_sq hb,

        have h_eqfunc : (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * (a - m)^ 2)) = (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * (a - m) ^ 2)))  ,
          ext x,
          simp,

        rw ← h_eqfunc,
        exact measure_theory.integrable.comp_sub_right h_gaussexp m,
      }
    },
    {
      --refine filter.germ.coe_le.mp _,
      refine filter.eventually_of_forall _,
      have hbp1 : 0 < s^2,
          exact (sq_pos_iff s).mpr h,
        -- have hbp2 : 0 < 2
      have hbp2 : 0 < 2*s^2,
          simp,
          exact hbp1,

      --have h_pipos : 0 < π,
        --exact pi_pos,
      have h_exppos : 0 < (2 * s ^ 2) * π,
        exact mul_pos hbp2 pi_pos,

      --simp at h_sqrt_pos,

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

lemma moment_one_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  μ[id] = m :=
begin
  rw real_gaussian at hμ,
  unfold gaussian_density at hμ, dsimp at *,
  simp [hs] at hμ,
  --rw hμ,
  sorry
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

  sorry
end

lemma std_gaussian_rv_const_smul (hf : std_gaussian_rv f) (hfmeas : measurable f) (s : ℝ) :
  gaussian_rv (s • f) 0 s :=
begin
  sorry
end

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
