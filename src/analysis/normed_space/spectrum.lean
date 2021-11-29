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

lemma mem_resolvent_set_of_nearby {a : A} {k k' : 𝕜} (hk : k ∈ ρ a)
  (hkk' : ∥k' - k∥ < ∥(↑hk.unit⁻¹ : A)∥⁻¹) :
  k' ∈ ρ a :=
begin
  refine (units.unit_of_nearby hk.unit (↑ₐk' - a) _).is_unit,
  calc ∥(↑ₐk' - a) - (↑ₐk - a)∥
       = ∥↑ₐ(k' - k)∥         : by rw [ring_hom.map_sub, sub_sub_sub_cancel_right]
  ...  = ∥k' - k∥ * ∥(1 : A)∥ : by rw [algebra.algebra_map_eq_smul_one,norm_smul]
  ...  = ∥k' - k∥             : by simp [normed_algebra.norm_one 𝕜 A]
  ...  < ∥↑hk.unit⁻¹∥⁻¹       : hkk',
end

lemma is_open_resolvent_set (a : A) : is_open (ρ a) :=
begin
  haveI := normed_algebra.nontrivial 𝕜 A,
  apply metric.is_open_iff.mpr,
  intros k hk,
  refine ⟨∥↑hk.unit⁻¹∥⁻¹, inv_pos.mpr (units.norm_pos (hk.unit⁻¹)), _⟩,
  intros k' hk',
  rw [metric.mem_ball, dist_eq_norm] at hk',
  exact mem_resolvent_set_of_nearby hk hk',
end

/-- The `resolvent_set` as a term of `opens 𝕜` -/
def open_resolvent_set (a : A) : topological_space.opens 𝕜 :=
⟨ρ a, is_open_resolvent_set a⟩

lemma is_closed (a : A) : is_closed (σ a) :=
is_open.is_closed_compl (is_open_resolvent_set a)

lemma mem_resolvent_of_norm_lt {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) :
  k ∈ ρ a :=
begin
  rw [resolvent_set,set.mem_set_of_eq,algebra.algebra_map_eq_smul_one],
  have k_pos := lt_of_le_of_lt (norm_nonneg a) h,
  let ku := units.mk0 k (ne_zero_of_norm_pos k_pos),
  have lt_one :=
    calc  ∥ku⁻¹ • a∥ = ∥↑ku⁻¹ • a∥   : rfl
      ...            = ∥(↑ku)⁻¹ • a∥ : by rw units.coe_inv' ku
      ...            = ∥k⁻¹∥ * ∥a∥   : norm_smul k⁻¹ a
      ...            = ∥k∥⁻¹ * ∥a∥   : by rw normed_field.norm_inv
      ...            < 1            : (inv_mul_lt_iff k_pos).mpr (by simp [h]),
  have : is_unit (1 - ku⁻¹ • a), from (units.one_sub (ku⁻¹ • a) lt_one).is_unit,
  rwa ←is_unit.smul_sub_iff_sub_inv_smul at this,
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

local notation `σ` := spectrum 𝕜
local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A


open asymptotics normed_ring ring

theorem resolvent_has_deriv_at {a : A} {k : 𝕜} (hk : k ∈ ρ a) :
  has_deriv_at (resolvent a) (-(resolvent a k)*(resolvent a k)) k :=
begin
  rw [has_deriv_at_iff_is_o_nhds_zero, resolvent_eq hk, is_o_iff],
  let ku := hk.unit,
  rcases is_O.exists_pos (inverse_add_norm_diff_second_order ku) with ⟨C,C_pos,hC⟩,
  rw is_O_with_iff at hC,
  intros c hc,
  simp only [filter.eventually_iff,metric.mem_nhds_iff] at hC ⊢,
  rcases hC with ⟨ε,ε_pos,hε⟩,
  use min (c*C⁻¹) ε,
  have hcC : c*C⁻¹ > 0, by nlinarith [inv_pos.mpr C_pos],
  split,
  { exact lt_min hcC ε_pos },
  { intros k' hk',
    simp only [lt_min_iff, mem_ball_zero_iff] at hk',
    have k'_mem : ↑ₐk' ∈ metric.ball (0 : A) ε, by simp [hk'.right],
    specialize hε k'_mem,
    rw set.mem_set_of_eq at hε,
    have res_add : resolvent a (k + k') = inverse (↑ₐk - a + ↑ₐk'),
      by { apply congr_arg inverse, rw ring_hom.map_add, noncomm_ring, },
    have k'_smul : k' • (-(↑ku⁻¹) * (↑ku⁻¹)) = -↑ku⁻¹ * ↑ₐk' * ↑ku⁻¹, by
      by { rw [←algebra.mul_smul_comm k', algebra.smul_def'], norm_cast, noncomm_ring },
    calc
      ∥resolvent a (k + k') - ↑ku⁻¹ - k' • (-(↑ku⁻¹) * (↑ku⁻¹))∥
          = ∥inverse (↑ₐk - a + ↑ₐk') - ↑ku⁻¹  + ↑ku⁻¹ * ↑ₐk' * ↑ku⁻¹∥ : by {rw [res_add,k'_smul], noncomm_ring}
      ... = ∥inverse (↑ku + ↑ₐk') - ↑ku⁻¹  + ↑ku⁻¹ * ↑ₐk' * ↑ku⁻¹∥ : rfl
      ... ≤ C * ∥∥↑ₐk'∥^2∥ : hε
      ... = C * ∥k'∥ * ∥k'∥ : by rw [real.norm_of_nonneg (pow_two_nonneg _),pow_two,mul_assoc,normed_algebra.norm_algebra_map_eq]
      ... ≤ C * ∥k'∥ * (c * C⁻¹) : mul_le_mul_of_nonneg_left (le_of_lt hk'.left) (by nlinarith [C_pos, norm_nonneg k'])
      ... = (C * C⁻¹) * c * ∥k'∥ : by ring
      ... = c * ∥k'∥ : by simp [mul_inv_cancel (ne_of_gt C_pos)],
    },
end

end resolvent_deriv

end spectrum
