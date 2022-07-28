import probability.density
import probability.moments
import analysis.special_functions.gaussian

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

def measure.real_gaussian (μ : measure ℝ) (m s : ℝ) : Prop :=
if s ≠ 0 then μ = (volume : measure ℝ).with_density (gaussian_density m s) else μ = measure.dirac m

open probability_theory measure

variables {μ : measure ℝ} {m s : ℝ}

lemma is_probability_measure_real_gaussian (hμ : μ.real_gaussian m s) :
  is_probability_measure μ :=
begin
  rw real_gaussian at hμ,
  split_ifs at hμ,
  { sorry }, -- the lemma `integral_gaussian` is useful!
  { exact hμ.symm ▸ measure.dirac.is_probability_measure }
end

lemma moment_one_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  moment id 1 μ = 0 :=
begin
  sorry
end

end measure_theory
