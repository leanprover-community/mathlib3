/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
import measure_theory.integral.interval_integral

/-!
# Integral over a torus in `ℂⁿ` and (n-dim) Cauchy Integral Formula?

In this file we will define in `torus_integrable` the integrability of functions
`f : ℂⁿ → E` over a torus, where `E` is a Banach Space with second countable topology
and we will give the definition of an integral over a torus in `torus_integral`, being the
`•`-product of the derivative of `torus_map` and `f (torus_map)`.
We will also prove the integrability of this product as well as prove some other basic
properties for both definitions.
The main goal will be

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
variables {E : Type*} [measurable_space E] [normed_group E]

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

/--A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/
def torus_integrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  integrable_on (λ (θ : ℝⁿ), f (torus_map c R θ)) (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume

--Constant functions are torus integrable
lemma torus_integrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) :
  torus_integrable (λ _, a) c R :=
begin
  simp [torus_integrable, measure_Icc_lt_top],
end

--If `f` is torus integrable then `-f` is torus integrable
lemma neg [borel_space E] {f : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ} (hf : torus_integrable f c R) :
  torus_integrable (-f) c R := hf.neg

--Addition `f + g` of two torus integrable functions `f, g` is torus integrable
lemma add [borel_space E] [second_countable_topology E]
  {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ} (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integrable (f + g) c R := hf.add hg

lemma torus_integrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} :
  torus_integrable f c 0 :=
begin
  rw [torus_integrable, torus_map_zero_radius],
  apply torus_integrable_const (f c) c 0,
end

/--The function given in the definition of `torus_integral` is integrable-/
lemma function_integrable [borel_space E] [normed_space ℂ E] [second_countable_topology E]
  (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) (hf : torus_integrable f c R) :
  integrable_on (λ (θ : ℝⁿ), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ))
                (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume :=
begin
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' _ _,
  { apply ae_measurable.smul,
    { apply continuous.ae_measurable,
    exact continuous_finset_prod finset.univ
    (λ (i : fin ↑n) (H : i ∈ finset.univ),
    continuous_const.mul
      (continuous_exp.comp ((is_R_or_C.continuous_of_real.comp (continuous_apply i)).mul continuous_const))) },
  exact hf.1 },
  simp [norm_smul, map_prod],
end

variables [borel_space E] [normed_space ℂ E] [second_countable_topology E] [complete_space E]

/--The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`
as the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/
def torus_integral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ)

lemma torus_integral_radius_zero (f : ℂⁿ → E) (c : ℂⁿ) :
  torus_integral f c 0 = 0 :=
begin
  simp [torus_integral],
end

lemma torus_integral_neg {f : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ} :
  -torus_integral f c R = torus_integral (-f) c R :=
begin
  repeat {rw torus_integral},
  simp,
  rw ← integral_neg,
end

lemma torus_integral_add {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}
  (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π),
  (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ) + (∏ i, I * R i * exp(θ i * I)) • g (torus_map c R θ)
  = (∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ))
  + (∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • g (torus_map c R θ)) :=
begin
  apply integral_add _ _,
  exact function_integrable f c R hf,
  exact function_integrable _ _ _ hg,
end

lemma torus_integral_add' {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}
  (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integral (f + g) c R = torus_integral f c R + torus_integral g c R :=
begin
  repeat {rw torus_integral},
  simp [mul_add],
  exact torus_integral_add hf hg,
end

lemma torus_integral_sub {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}
  (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π),
  (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ) - (∏ i, I * R i * exp(θ i * I)) • g (torus_map c R θ)
  = (∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ))
  - (∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • g (torus_map c R θ)) :=
begin
  rw [sub_eq_add_neg, ← torus_integral, ← torus_integral,
      torus_integral_neg, ← torus_integral_add' hf (neg hg), torus_integral],
  simp [smul_add, sub_eq_add_neg],
end

lemma torus_integral_smul {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  (a : 𝕜) (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), a • ((∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ))
  = a • ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ) :=
begin
  exact integral_smul _ _,
end

lemma torus_integral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
  ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), a * ((∏ i, I * R i * exp(θ i * I)) * f (torus_map c R θ))
  = a * ∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) * f (torus_map c R θ) :=
begin
  exact torus_integral_smul a f c R,
end

/--If for all `θ : ℝⁿ`, `∥f (torus_map c R θ)∥` is less than or equal to a constant `C : ℝ`, then
`∥∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ)∥`
is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/
lemma norm_integral_le_of_norm_le_const {f : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ} {C : ℝ}
  (hf : ∀ θ, ∥f (torus_map c R θ)∥ ≤ C) :
  ∥∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ)∥
    ≤ (2 * π)^(n: ℕ) * (∏ i, |R i|) * C :=
begin
  have h1 : ∥∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π),
             (∏ i, I * R i * exp(θ i * I)) • f (torus_map c R θ)∥
             ≤ (∏ i, |R i|) * C * (volume (Icc (0 : ℝⁿ) (λ _, 2 * π))).to_real,
  { apply norm_set_integral_le_of_norm_le_const' _ _ _,
   exact measure_Icc_lt_top,
   exact measurable_set_Icc,
   { intros x h2,
    simp [norm_smul],
    apply mul_le_mul_of_nonneg_left (hf x) _,
    apply multiset.prod_induction _ _ _ _ _,
    { intros a b ha hb,
     exact mul_nonneg ha hb },
    exact zero_le_one,
    { intros a ha,
     simp at ha,
     cases ha with i ha,
     rw ← ha,
     apply _root_.abs_nonneg } } },
  rw real.volume_Icc_pi_to_real _ at h1,
  { simp at h1,
   rw [mul_comm (∏ i, |R i|) C, mul_assoc] at h1,
   rwa [mul_comm ((2 * π)^(n : ℕ) * ∏ i, |R i|) C, mul_comm ((2 * π)^(n : ℕ)) (∏ i, |R i|)] },
  refine pi.le_def.mpr _,
  intro i,
  apply le_of_lt,
  exact real.two_pi_pos,
end
