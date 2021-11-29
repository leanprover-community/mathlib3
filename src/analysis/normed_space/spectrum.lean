/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.spectrum
import analysis.calculus.deriv
/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius`: supremum of `abs k` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `is_open_resolvent_set`: the resolvent set is open.
* `is_closed`: the spectrum is closed.
* `subset_closed_ball_norm`: the spectrum is a subset of closed disk of radius equal to the norm.
* `is_compact`: the spectrum is compact.
* `spectral_radius_le_norm`: the spectral radius is bounded above by the norm.
* `resolvent_has_deriv_at`: the resolvent function is differentiable on the resolvent set.


## TODO

* after we have Liouville's theorem, prove that the spectrum is nonempty when the
  scalar field is ℂ.
* compute all derivatives of `resolvent a`.

-/

open_locale ennreal

/-- The *spectral radius* is the supremum of the `nnnorm` (`∥⬝∥₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞` so that it lives in a `complete_lattice`. Note that it
    is possible for `spectrum 𝕜 a = ∅`. In this case, `spectral_radius a = 0`-/
noncomputable def spectral_radius (𝕜 : Type*) {A : Type*} [normed_field 𝕜] [ring A]
  [algebra 𝕜 A] (a : A) : ℝ≥0∞ :=
⨆ k ∈ spectrum 𝕜 a, ∥k∥₊

namespace spectrum

section spectrum_compact

variables {𝕜 : Type*} {A : Type*}
variables [normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]

local notation `σ` := spectrum 𝕜
local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

lemma is_open_resolvent_set (a : A) : is_open (ρ a) :=
units.is_open.preimage ((algebra_map_isometry 𝕜 A).continuous.sub continuous_const)

lemma is_closed (a : A) : is_closed (σ a) :=
(is_open_resolvent_set a).is_closed_compl

lemma mem_resolvent_of_norm_lt {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) :
  k ∈ ρ a :=
begin
  rw [resolvent_set,set.mem_set_of_eq,algebra.algebra_map_eq_smul_one],
  have hk : k ≠ 0 := ne_zero_of_norm_pos (by linarith [norm_nonneg a]),
  let ku := units.map (↑ₐ).to_monoid_hom (units.mk0 k hk),
  have hku : ∥-a∥ < ∥(↑ku⁻¹:A)∥⁻¹ := by simpa [ku, algebra_map_isometry] using h,
  simpa [ku, sub_eq_add_neg, algebra.algebra_map_eq_smul_one] using (ku.add (-a) hku).is_unit,
end

lemma norm_le_norm_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) :
  ∥k∥ ≤ ∥a∥ :=
le_of_not_lt (not_imp_not.mpr mem_resolvent_of_norm_lt hk)

lemma subset_closed_ball_norm (a : A) :
  σ a ⊆ metric.closed_ball (0 : 𝕜) (∥a∥) :=
λ k hk, by simp [norm_le_norm_of_mem hk]

lemma is_bounded (a : A) : metric.bounded (σ a) :=
(metric.bounded_iff_subset_ball 0).mpr ⟨∥a∥, subset_closed_ball_norm a⟩

theorem is_compact [proper_space 𝕜] (a : A) : is_compact (σ a) :=
metric.is_compact_of_is_closed_bounded (is_closed a) (is_bounded a)

theorem spectral_radius_le_nnnorm (a : A) :
  spectral_radius 𝕜 a ≤ ∥a∥₊ :=
begin
  suffices h : ∀ (k : 𝕜) (hk : k ∈ σ a), (∥k∥₊ : ℝ≥0∞) ≤ ∥a∥₊,
  { exact bsupr_le h, },
  { by_cases ha : (σ a).nonempty,
    { intros _ hk, exact_mod_cast norm_le_norm_of_mem hk },
    { rw set.not_nonempty_iff_eq_empty at ha,
      simp [ha, set.ball_empty_iff] } }
end

end spectrum_compact

section resolvent_deriv

variables {𝕜 : Type*} {A : Type*}
variables [nondiscrete_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]

local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

theorem has_deriv_at_resolvent {a : A} {k : 𝕜} (hk : k ∈ ρ a) :
  has_deriv_at (resolvent a) (-(resolvent a k) * (resolvent a k)) k :=
begin
  have H₁ : has_fderiv_at ring.inverse _ (↑ₐk - a) := has_fderiv_at_ring_inverse hk.unit,
  have H₂ : has_deriv_at (λ k, ↑ₐk - a) 1 k,
  { simpa using (algebra.linear_map 𝕜 A).has_deriv_at.sub_const a },
  simpa [resolvent, hk.unit_spec, ← ring.inverse_unit hk.unit] using H₁.comp_has_deriv_at k H₂,
end

end resolvent_deriv

end spectrum
