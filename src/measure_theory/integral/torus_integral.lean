/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
import measure_theory.integral.interval_integral

/-!
# Integral over a torus in `ℂⁿ` and (n-dim) Cauchy Integral Formula?

In this file we will define in `torus_integrable` the integrability of functions `f : ℂⁿ → E` over a
torus, where `E` is a Banach Space, and we will give the definition of an integral over a torus in
`torus_integral`, being the `•`-product of the derivative of `torus_map` and `f (torus_map)`.  We
will also prove the integrability of this product as well as prove some other basic properties for
both definitions.  The main goal will be

## Main definitions

* `torus_map c R`: the generalized multidimensional exponential map from $ℝⁿ → ℂⁿ$ defined
  as $θ ↦ c_i + R_ie^{θ_i * i}$, with $R ∈ ℝⁿ$;

* `torus_integrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` if `f ∘ torus_map c R` is integrable on the
  closed set `Icc (0 : ℝⁿ) (λ _, 2 * π)`;

* `torus_integral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\int_{[0, 2 * π]} (∏_{i = 1}^{n} I * R_i * e^{θ_i * i}) • f (c + Re^{θ_i * i})\,dθ_i$;

## Main statements

-/

variable {n : ℕ+}
variables {E : Type*} [normed_group E]

noncomputable theory

open complex set measure_theory function filter topological_space
open_locale real big_operators

local notation `ℝⁿ`:= fin n → ℝ
local notation `ℂⁿ`:= fin n → ℂ

/-!
### `torus_map`, a generalization of a torus
-/

/-- The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
it to every n axis. -/
def torus_map (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ :=
  λ θ i, c i + R i * exp(θ i * I)

lemma periodic_torus_map (c : ℂⁿ) (R : ℝⁿ) : periodic (torus_map c R) (λ _, 2 * π) :=
begin
  intro θ,
  rw torus_map,
  simp [add_mul, exp_periodic _],
end

lemma torus_map_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) :
  torus_map c R θ - c = torus_map 0 R θ :=
begin
  rw [torus_map, torus_map],
  dsimp,
  ext i,
  simp,
  simp,
end

lemma torus_map_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} :
  torus_map c R θ = c ↔ R = 0 :=
begin
  simp [funext_iff, torus_map, exp_ne_zero],
end

@[simp] lemma torus_map_zero_radius (c : ℂⁿ) : torus_map c 0 = const ℝⁿ c :=
begin
  ext θ i,
  repeat {conv_lhs {rw torus_map_eq_center_iff.2}},
end

/-!
### Integrability of a function on a generalized torus
-/

/-- A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/
def torus_integrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  integrable_on (λ (θ : ℝⁿ), f (torus_map c R θ)) (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume

namespace torus_integrable

variables {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- Constant functions are torus integrable -/
lemma torus_integrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) :
  torus_integrable (λ _, a) c R :=
by simp [torus_integrable, measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected lemma neg (hf : torus_integrable f c R) : torus_integrable (-f) c R := hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected lemma add (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integrable (f + g) c R :=
hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected lemma sub (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integrable (f - g) c R :=
hf.sub hg

lemma torus_integrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} :
  torus_integrable f c 0 :=
begin
  rw [torus_integrable, torus_map_zero_radius],
  apply torus_integrable_const (f c) c 0,
end

/--The function given in the definition of `torus_integral` is integrable-/
lemma function_integrable [normed_space ℂ E] (hf : torus_integrable f c R) :
  integrable_on (λ (θ : ℝⁿ), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ))
                (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume :=
begin
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' _ _,
  { refine (continuous.ae_strongly_measurable _).smul hf.1,
    exact continuous_finset_prod finset.univ (λ i hi, continuous_const.mul
      (((continuous_of_real.comp (continuous_apply i)).mul continuous_const).cexp)) },
  simp [norm_smul, map_prod],
end

end torus_integrable

variables [normed_space ℂ E] [complete_space E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/--The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`
as the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/
def torus_integral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ)

notation `∯` binders ` in ` `T(` c `, ` R `)` `, ` r:(scoped:60 f, torus_integral f c R) := r

lemma torus_integral_radius_zero (f : ℂⁿ → E) (c : ℂⁿ) : ∯ x in T(c, 0), f x = 0 :=
by simp only [torus_integral, pi.zero_apply, of_real_zero, mul_zero, zero_mul, fin.prod_const,
  zero_pow' n n.ne_zero, not_false_iff, zero_smul, integral_zero]

lemma torus_integral_neg (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), -f x = -∯ x in T(c, R), f x :=
by simp [torus_integral, integral_neg]

lemma torus_integral_add (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∯ x in T(c, R), f x + g x = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x :=
by simpa only [torus_integral, smul_add, pi.add_apply]
  using integral_add hf.function_integrable hg.function_integrable

lemma torus_integral_sub (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∯ x in T(c, R), f x - g x = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x :=
by simpa only [sub_eq_add_neg, ← torus_integral_neg] using torus_integral_add hf hg.neg

lemma torus_integral_smul {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] [smul_comm_class 𝕜 ℂ E]
  (a : 𝕜) (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), a • f x = a • ∯ x in T(c, R), f x :=
by simp only [torus_integral, integral_smul, ← smul_comm a]

lemma torus_integral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), a * f x = a * ∯ x in T(c, R), f x :=
torus_integral_smul a f c R

/--If for all `θ : ℝⁿ`, `∥f (torus_map c R θ)∥` is less than or equal to a constant `C : ℝ`, then
`∥∯ x in T(c, R), f x∥` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/
lemma norm_torus_integral_le_of_norm_le_const {C : ℝ} (hf : ∀ θ, ∥f (torus_map c R θ)∥ ≤ C) :
  ∥∯ x in T(c, R), f x∥ ≤ (2 * π)^(n: ℕ) * (∏ i, |R i|) * C :=
calc ∥∯ x in T(c, R), f x∥ ≤ (∏ i, |R i|) * C * (volume (Icc (0 : ℝⁿ) (λ _, 2 * π))).to_real :
  norm_set_integral_le_of_norm_le_const' measure_Icc_lt_top measurable_set_Icc $ λ θ hθ,
    ( calc ∥(∏ i : fin n, I * R i * exp (θ i * I)) • f (torus_map c R θ)∥
          = (∏ i : fin n, |R i|) * ∥f (torus_map c R θ)∥ : by simp [norm_smul]
      ... ≤ (∏ i : fin n, |R i|) * C :
        mul_le_mul_of_nonneg_left (hf _) (finset.prod_nonneg $ λ _ _, abs_nonneg _) )
... = (2 * π)^(n: ℕ) * (∏ i, |R i|) * C :
  by simp only [pi.zero_def, real.volume_Icc_pi_to_real (λ _, real.two_pi_pos.le), sub_zero,
      fin.prod_const, mul_assoc, mul_comm ((2 * π) ^ (n : ℕ))]
