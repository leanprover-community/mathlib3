/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.spectrum
import analysis.special_functions.pow
import analysis.special_functions.exponential
import analysis.complex.liouville
import analysis.analytic.radius_liminf
import topology.algebra.module.character_space
/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius : ℝ≥0∞`: supremum of `∥k∥₊` for all `k ∈ spectrum 𝕜 a`
* `normed_ring.alg_equiv_complex_of_complete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Main statements

* `spectrum.is_open_resolvent_set`: the resolvent set is open.
* `spectrum.is_closed`: the spectrum is closed.
* `spectrum.subset_closed_ball_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.is_compact`: the spectrum is compact.
* `spectrum.spectral_radius_le_nnnorm`: the spectral radius is bounded above by the norm.
* `spectrum.has_deriv_at_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.


## TODO

* compute all derivatives of `resolvent a`.

-/

open_locale ennreal

--prereqs

open filter

open_locale nnreal

lemma nnreal.eventually_pow_one_div_le (x : ℝ≥0) {ε : ℝ≥0} (hε : 1 < ε) :
  ∀ᶠ (n : ℕ) in at_top, x ^ (1 / n : ℝ) ≤ ε :=
begin
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hε),
  rw [tsub_add_cancel_of_le hε.le] at hm,
  refine eventually_at_top.2 ⟨m + 1, λ n hn, _⟩,
  simpa only [nnreal.rpow_one_div_le_iff (nat.cast_pos.2 $ m.succ_pos.trans_le hn),
    nnreal.rpow_nat_cast] using hm.le.trans (pow_le_pow hε.le (m.le_succ.trans hn)),
end

lemma ennreal.eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {ε : ℝ≥0∞} (hε : 1 < ε) :
  ∀ᶠ (n : ℕ) in at_top, x ^ (1 / n : ℝ) ≤ ε :=
begin
  lift x to ℝ≥0 using hx,
  by_cases ε = ∞,
  refine eventually_of_forall (λ n, h.symm ▸ le_top),
  lift ε to ℝ≥0 using h,
  have := nnreal.eventually_pow_one_div_le x (by exact_mod_cast hε : 1 < ε),
  refine this.congr (eventually_of_forall $ λ n, _),
  rw [ennreal.coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), ennreal.coe_le_coe],
end


--prereqs


/-- The *spectral radius* is the supremum of the `nnnorm` (`∥⬝∥₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
    case, `spectral_radius a = 0`.  It is also possible that `spectrum 𝕜 a` be unbounded (though
    not for Banach algebras, see `spectrum.is_bounded`, below).  In this case,
    `spectral_radius a = ∞`. -/
noncomputable def spectral_radius (𝕜 : Type*) {A : Type*} [normed_field 𝕜] [ring A]
  [algebra 𝕜 A] (a : A) : ℝ≥0∞ :=
⨆ k ∈ spectrum 𝕜 a, ∥k∥₊

variables {𝕜 : Type*} {A : Type*}

namespace spectrum

section spectrum_compact

variables [nontrivially_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A]

local notation `σ` := spectrum 𝕜
local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

@[simp] lemma spectral_radius.of_subsingleton [subsingleton A] (a : A) :
  spectral_radius 𝕜 a = 0 :=
by simp [spectral_radius]

@[simp] lemma spectral_radius_zero : spectral_radius 𝕜 (0 : A) = 0 :=
by { nontriviality A, simp [spectral_radius] }

lemma mem_resolvent_set_of_spectral_radius_lt {a : A} {k : 𝕜} (h : spectral_radius 𝕜 a < ∥k∥₊) :
  k ∈ ρ a :=
not_not.mp $ λ hn, h.not_le $ le_supr₂ k hn

variable [complete_space A]

lemma is_open_resolvent_set (a : A) : is_open (ρ a) :=
units.is_open.preimage ((continuous_algebra_map 𝕜 A).sub continuous_const)

protected lemma is_closed (a : A) : is_closed (σ a) :=
(is_open_resolvent_set a).is_closed_compl

lemma mem_resolvent_set_of_norm_lt_mul {a : A} {k : 𝕜} (h : ∥a∥ * ∥(1 : A)∥ < ∥k∥) :
  k ∈ ρ a :=
begin
  rw [resolvent_set, set.mem_set_of_eq, algebra.algebra_map_eq_smul_one],
  nontriviality A,
  have hk : k ≠ 0,
    from ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne',
  let ku := units.map (↑ₐ).to_monoid_hom (units.mk0 k hk),
  rw [←inv_inv (∥(1 : A)∥), mul_inv_lt_iff (inv_pos.2 $ norm_pos_iff.2 (one_ne_zero : (1 : A) ≠ 0))]
    at h,
  have hku : ∥-a∥ < ∥(↑ku⁻¹:A)∥⁻¹ := by simpa [ku, norm_algebra_map] using h,
  simpa [ku, sub_eq_add_neg, algebra.algebra_map_eq_smul_one] using (ku.add (-a) hku).is_unit,
end

lemma mem_resolvent_set_of_norm_lt [norm_one_class A] {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) :
  k ∈ ρ a :=
mem_resolvent_set_of_norm_lt_mul (by rwa [norm_one, mul_one])

lemma norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) :
  ∥k∥ ≤ ∥a∥ * ∥(1 : A)∥ :=
le_of_not_lt $ mt mem_resolvent_set_of_norm_lt_mul hk

lemma norm_le_norm_of_mem [norm_one_class A] {a : A} {k : 𝕜} (hk : k ∈ σ a) :
  ∥k∥ ≤ ∥a∥ :=
le_of_not_lt $ mt mem_resolvent_set_of_norm_lt hk

lemma subset_closed_ball_norm_mul (a : A) :
  σ a ⊆ metric.closed_ball (0 : 𝕜) (∥a∥ * ∥(1 : A)∥) :=
λ k hk, by simp [norm_le_norm_mul_of_mem hk]

lemma subset_closed_ball_norm [norm_one_class A] (a : A) :
  σ a ⊆ metric.closed_ball (0 : 𝕜) (∥a∥) :=
λ k hk, by simp [norm_le_norm_of_mem hk]

lemma is_bounded (a : A) : metric.bounded (σ a) :=
(metric.bounded_iff_subset_ball 0).mpr ⟨∥a∥ * ∥(1 : A)∥, subset_closed_ball_norm_mul a⟩

protected theorem is_compact [proper_space 𝕜] (a : A) : is_compact (σ a) :=
metric.is_compact_of_is_closed_bounded (spectrum.is_closed a) (is_bounded a)

theorem spectral_radius_le_nnnorm [norm_one_class A] (a : A) :
  spectral_radius 𝕜 a ≤ ∥a∥₊ :=
by { refine supr₂_le (λ k hk, _), exact_mod_cast norm_le_norm_of_mem hk }

open ennreal polynomial

variable (𝕜)
theorem spectral_radius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
  spectral_radius 𝕜 a ≤ (∥a ^ (n + 1)∥₊) ^ (1 / (n + 1) : ℝ) * (∥(1 : A)∥₊) ^ (1 / (n + 1) : ℝ) :=
begin
  refine supr₂_le (λ k hk, _),
  /- apply easy direction of the spectral mapping theorem for polynomials -/
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)),
    by simpa only [one_mul, algebra.algebra_map_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (monomial (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩,
  /- power of the norm is bounded by norm of the power -/
  have nnnorm_pow_le : (↑(∥k∥₊ ^ (n + 1)) : ℝ≥0∞) ≤ ∥a ^ (n + 1)∥₊ * ∥(1 : A)∥₊,
    { simpa only [real.to_nnreal_mul (norm_nonneg _), norm_to_nnreal, nnnorm_pow k (n + 1),
        ennreal.coe_mul] using coe_mono (real.to_nnreal_mono (norm_le_norm_mul_of_mem pow_mem)) },
  /- take (n + 1)ᵗʰ roots and clean up the left-hand side -/
  have hn : 0 < ((n + 1 : ℕ) : ℝ), by exact_mod_cast nat.succ_pos',
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le,
  erw [coe_pow, ←rpow_nat_cast, ←rpow_mul, mul_one_div_cancel hn.ne', rpow_one],
  rw [nat.cast_succ, ennreal.coe_mul_rpow],
end

theorem spectral_radius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
  spectral_radius 𝕜 a ≤ at_top.liminf (λ n : ℕ, (∥a ^ n∥₊ : ℝ≥0∞) ^ (1 / n : ℝ)) :=
begin
  refine ennreal.le_of_forall_lt_one_mul_le (λ ε hε, _),
  by_cases ε = 0,
  { simp only [h, zero_mul, zero_le'] },
  have hε' : ε⁻¹ ≠ ∞,
    from λ h', h (by simpa only [inv_inv, inv_top] using congr_arg (λ (x : ℝ≥0∞), x⁻¹) h'),
  simp only [ennreal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_supr_infi_of_nat', ennreal.supr_mul, ennreal.infi_mul hε'],
  rw [←ennreal.inv_lt_inv, inv_one] at hε,
  obtain ⟨N, hN⟩ := eventually_at_top.mp (ennreal.eventually_pow_one_div_le (ennreal.coe_ne_top : ↑∥(1 : A)∥₊ ≠ ∞) hε),
  refine (le_trans _ (le_supr _ (N + 1))),
  refine le_infi (λ n, _),
  simp only [←add_assoc],
  refine (spectral_radius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans _,
  norm_cast,
  exact mul_le_mul_left' (hN (n + N + 1) (by linarith)) _,
end

end spectrum_compact

section resolvent

open filter asymptotics

variables [nontrivially_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]

local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

theorem has_deriv_at_resolvent {a : A} {k : 𝕜} (hk : k ∈ ρ a) :
  has_deriv_at (resolvent a) (-(resolvent a k) ^ 2) k :=
begin
  have H₁ : has_fderiv_at ring.inverse _ (↑ₐk - a) := has_fderiv_at_ring_inverse hk.unit,
  have H₂ : has_deriv_at (λ k, ↑ₐk - a) 1 k,
  { simpa using (algebra.linear_map 𝕜 A).has_deriv_at.sub_const a },
  simpa [resolvent, sq, hk.unit_spec, ← ring.inverse_unit hk.unit] using H₁.comp_has_deriv_at k H₂,
end

/- TODO: Once there is sufficient API for bornology, we should get a nice filter / asymptotics
version of this, for example: `tendsto (resolvent a) (cobounded 𝕜) (𝓝 0)` or more specifically
`(resolvent a) =O[cobounded 𝕜] (λ z, z⁻¹)`. -/
lemma norm_resolvent_le_forall (a : A) :
  ∀ ε > 0, ∃ R > 0, ∀ z : 𝕜, R ≤ ∥z∥ → ∥resolvent a z∥ ≤ ε :=
begin
  obtain ⟨c, c_pos, hc⟩ := (@normed_ring.inverse_one_sub_norm A _ _).exists_pos,
  rw [is_O_with_iff, eventually_iff, metric.mem_nhds_iff] at hc,
  rcases hc with ⟨δ, δ_pos, hδ⟩,
  simp only [cstar_ring.norm_one, mul_one] at hδ,
  intros ε hε,
  have ha₁ : 0 < ∥a∥ + 1 := lt_of_le_of_lt (norm_nonneg a) (lt_add_one _),
  have min_pos : 0 < min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹),
    from lt_min (mul_pos δ_pos (inv_pos.mpr ha₁)) (mul_pos hε (inv_pos.mpr c_pos)),
  refine ⟨(min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹))⁻¹, inv_pos.mpr min_pos, (λ z hz, _)⟩,
  have hnz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inv_pos.mpr min_pos) hz),
  replace hz := inv_le_of_inv_le min_pos hz,
  rcases (⟨units.mk0 z hnz, units.coe_mk0 hnz⟩ : is_unit z) with ⟨z, rfl⟩,
  have lt_δ : ∥z⁻¹ • a∥ < δ,
  { rw [units.smul_def, norm_smul, units.coe_inv, norm_inv],
    calc ∥(z : 𝕜)∥⁻¹ * ∥a∥ ≤ δ * (∥a∥ + 1)⁻¹ * ∥a∥
        : mul_le_mul_of_nonneg_right (hz.trans (min_le_left _ _)) (norm_nonneg _)
    ...                   < δ
        : by { conv { rw mul_assoc, to_rhs, rw (mul_one δ).symm },
               exact mul_lt_mul_of_pos_left
                 ((inv_mul_lt_iff ha₁).mpr ((mul_one (∥a∥ + 1)).symm ▸ (lt_add_one _))) δ_pos } },
  rw [←inv_smul_smul z (resolvent a (z : 𝕜)), units_smul_resolvent_self, resolvent,
    algebra.algebra_map_eq_smul_one, one_smul, units.smul_def, norm_smul, units.coe_inv, norm_inv],
  calc _ ≤ ε * c⁻¹ * c : mul_le_mul (hz.trans (min_le_right _ _)) (hδ (mem_ball_zero_iff.mpr lt_δ))
                           (norm_nonneg _) (mul_pos hε (inv_pos.mpr c_pos)).le
  ...    = _           : inv_mul_cancel_right₀ c_pos.ne.symm ε,
end

end resolvent

section one_sub_smul

open continuous_multilinear_map ennreal formal_multilinear_series
open_locale nnreal ennreal

variables
[nontrivially_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A]

variable (𝕜)
/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `∥a∥₊⁻¹`. -/
lemma has_fpower_series_on_ball_inverse_one_sub_smul [complete_space A] (a : A) :
  has_fpower_series_on_ball (λ z : 𝕜, ring.inverse (1 - z • a))
    (λ n, continuous_multilinear_map.mk_pi_field 𝕜 (fin n) (a ^ n)) 0 (∥a∥₊)⁻¹ :=
{ r_le :=
  begin
    refine le_of_forall_nnreal_lt (λ r hr, le_radius_of_bound_nnreal _ (max 1 ∥(1 : A)∥₊) (λ n, _)),
    rw [←norm_to_nnreal, norm_mk_pi_field, norm_to_nnreal],
    cases n,
    { simp only [le_refl, mul_one, or_true, le_max_iff, pow_zero] },
    { refine le_trans (le_trans (mul_le_mul_right' (nnnorm_pow_le' a n.succ_pos) (r ^ n.succ)) _)
        (le_max_left _ _),
      { by_cases ∥a∥₊ = 0,
        { simp only [h, zero_mul, zero_le', pow_succ], },
        { rw [←coe_inv h, coe_lt_coe, nnreal.lt_inv_iff_mul_lt h] at hr,
          simpa only [←mul_pow, mul_comm] using pow_le_one' hr.le n.succ } } }
  end,
  r_pos := ennreal.inv_pos.mpr coe_ne_top,
  has_sum := λ y hy,
  begin
    have norm_lt : ∥y • a∥ < 1,
    { by_cases h : ∥a∥₊ = 0,
      { simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero] },
      { have nnnorm_lt : ∥y∥₊ < ∥a∥₊⁻¹,
          by simpa only [←coe_inv h, mem_ball_zero_iff, metric.emetric_ball_nnreal] using hy,
        rwa [←coe_nnnorm, ←real.lt_to_nnreal_iff_coe_lt, real.to_nnreal_one, nnnorm_smul,
          ←nnreal.lt_inv_iff_mul_lt h] } },
    simpa [←smul_pow, (normed_ring.summable_geometric_of_norm_lt_1 _ norm_lt).has_sum_iff]
      using (normed_ring.inverse_one_sub _ norm_lt).symm,
  end }

variable {𝕜}
lemma is_unit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑∥z∥₊ < (spectral_radius 𝕜 a)⁻¹) :
  is_unit (1 - z • a) :=
begin
  by_cases hz : z = 0,
  { simp only [hz, is_unit_one, sub_zero, zero_smul] },
  { let u := units.mk0 z hz,
    suffices hu : is_unit (u⁻¹ • 1 - a),
    { rwa [is_unit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu },
    { rw [units.smul_def, ←algebra.algebra_map_eq_smul_one, ←mem_resolvent_set_iff],
      refine mem_resolvent_set_of_spectral_radius_lt _,
      rwa [units.coe_inv, nnnorm_inv, coe_inv (nnnorm_ne_zero_iff.mpr
        (units.coe_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)), lt_inv_iff_lt_inv] } }
end

/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `λ z, (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectral_radius 𝕜 a)⁻¹`. -/
theorem differentiable_on_inverse_one_sub_smul [complete_space A] {a : A} {r : ℝ≥0}
  (hr : (r : ℝ≥0∞) < (spectral_radius 𝕜 a)⁻¹) :
  differentiable_on 𝕜 (λ z : 𝕜, ring.inverse (1 - z • a)) (metric.closed_ball 0 r) :=
begin
  intros z z_mem,
  apply differentiable_at.differentiable_within_at,
  have hu : is_unit (1 - z • a),
  { refine is_unit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono _) hr),
    simpa only [norm_to_nnreal, real.to_nnreal_coe]
      using real.to_nnreal_mono (mem_closed_ball_zero_iff.mp z_mem) },
  have H₁ : differentiable 𝕜 (λ w : 𝕜, 1 - w • a) := (differentiable_id.smul_const a).const_sub 1,
  exact differentiable_at.comp z (differentiable_at_inverse hu.unit) (H₁.differentiable_at),
end

end one_sub_smul

section gelfand_formula

open filter ennreal continuous_multilinear_map
open_locale topological_space

variables
[normed_ring A] [normed_algebra ℂ A] [complete_space A]

/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
lemma limsup_pow_nnnorm_pow_one_div_le_spectral_radius (a : A) :
  limsup at_top (λ n : ℕ, ↑∥a ^ n∥₊ ^ (1 / n : ℝ)) ≤ spectral_radius ℂ a :=
begin
  refine ennreal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt (λ r r_pos r_lt, _)),
  simp_rw [inv_limsup, ←one_div],
  let p : formal_multilinear_series ℂ ℂ A :=
    λ n, continuous_multilinear_map.mk_pi_field ℂ (fin n) (a ^ n),
  suffices h : (r : ℝ≥0∞) ≤ p.radius,
  { convert h,
    simp only [p.radius_eq_liminf, ←norm_to_nnreal, norm_mk_pi_field],
    refine congr_arg _ (funext (λ n, congr_arg _ _)),
    rw [norm_to_nnreal, ennreal.coe_rpow_def (∥a ^ n∥₊) (1 / n : ℝ), if_neg],
    exact λ ha, by linarith [ha.2, (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ))], },
  { have H₁ := (differentiable_on_inverse_one_sub_smul r_lt).has_fpower_series_on_ball r_pos,
    exact ((has_fpower_series_on_ball_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le, }
end

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
  tendsto (λ n : ℕ, ((∥a ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞)) at_top (𝓝 (spectral_radius ℂ a)) :=
tendsto_of_le_liminf_of_limsup_le (spectral_radius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
  (limsup_pow_nnnorm_pow_one_div_le_spectral_radius a)

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
  tendsto (λ n : ℕ,  ennreal.of_real (∥a ^ n∥ ^ (1 / n : ℝ))) at_top (𝓝 (spectral_radius ℂ a)) :=
begin
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a,
  ext1,
  rw [←of_real_rpow_of_nonneg (norm_nonneg _) _, ←coe_nnnorm, coe_nnreal_eq],
  exact one_div_nonneg.mpr (by exact_mod_cast zero_le _),
end

end gelfand_formula

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
theorem nonempty {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
  [nontrivial A]
  (a : A) : (spectrum ℂ a).nonempty :=
begin
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent`
  is differentiable on `ℂ`. -/
  rw ←set.ne_empty_iff_nonempty,
  by_contra h,
  have H₀ : resolvent_set ℂ a = set.univ, by rwa [spectrum, set.compl_empty_iff] at h,
  have H₁ : differentiable ℂ (λ z : ℂ, resolvent a z), from λ z,
    (has_deriv_at_resolvent (H₀.symm ▸ set.mem_univ z : z ∈ resolvent_set ℂ a)).differentiable_at,
  /- The norm of the resolvent is small for all sufficently large `z`, and by compactness and
  continuity it is bounded on the complement of a large ball, thus uniformly bounded on `ℂ`.
  By Liouville's theorem `λ z, resolvent a z` is constant -/
  have H₂ := norm_resolvent_le_forall a,
  have H₃ : ∀ z : ℂ, resolvent a z = resolvent a (0 : ℂ),
  { refine λ z, H₁.apply_eq_apply_of_bounded (bounded_iff_exists_norm_le.mpr _) z 0,
    rcases H₂ 1 zero_lt_one with ⟨R, R_pos, hR⟩,
    rcases (proper_space.is_compact_closed_ball (0 : ℂ) R).exists_bound_of_continuous_on
      H₁.continuous.continuous_on with ⟨C, hC⟩,
    use max C 1,
    rintros _ ⟨w, rfl⟩,
    refine or.elim (em (∥w∥ ≤ R)) (λ hw, _) (λ hw, _),
      { exact (hC w (mem_closed_ball_zero_iff.mpr hw)).trans (le_max_left _ _) },
      { exact (hR w (not_le.mp hw).le).trans (le_max_right _ _), }, },
  /- `resolvent a 0 = 0`, which is a contradition because it isn't a unit. -/
  have H₅ : resolvent a (0 : ℂ) = 0,
  { refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg _)),
    rcases H₂ ε hε with ⟨R, R_pos, hR⟩,
    simpa only [H₃ R] using (zero_add ε).symm.subst
      (hR R (by exact_mod_cast (real.norm_of_nonneg R_pos.lt.le).symm.le)), },
  /- `not_is_unit_zero` is where we need `nontrivial A`, it is unavoidable. -/
  exact not_is_unit_zero (H₅.subst (is_unit_resolvent.mp
    (mem_resolvent_set_iff.mp (H₀.symm ▸ set.mem_univ 0)))),
end

section gelfand_mazur_isomorphism

variables [normed_ring A] [normed_algebra ℂ A] (hA : ∀ {a : A}, is_unit a ↔ a ≠ 0)
include hA

local notation `σ` := spectrum ℂ

lemma algebra_map_eq_of_mem {a : A} {z : ℂ} (h : z ∈ σ a) : algebra_map ℂ A z = a :=
by rwa [mem_iff, hA, not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebra_map ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebra_map_isometry` guarantees this map is an isometry.

Note: because `normed_division_ring` requires the field `norm_mul' : ∀ a b, ∥a * b∥ = ∥a∥ * ∥b∥`, we
don't use this type class and instead opt for a `normed_ring` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`normed_division_ring`, one may fill in the argument `hA` with the lemma `is_unit_iff_ne_zero`. -/
@[simps]
noncomputable def _root_.normed_ring.alg_equiv_complex_of_complete
  [complete_space A] : ℂ ≃ₐ[ℂ] A :=
let nt : nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩ in
{ to_fun := algebra_map ℂ A,
  inv_fun := λ a, (@spectrum.nonempty _ _ _ _ nt a).some,
  left_inv := λ z, by simpa only [@scalar_eq _ _ _ _ _ nt _] using
    (@spectrum.nonempty _ _ _ _ nt $ algebra_map ℂ A z).some_mem,
  right_inv := λ a, algebra_map_eq_of_mem @hA (@spectrum.nonempty _ _ _ _ nt a).some_mem,
  ..algebra.of_id ℂ A }

end gelfand_mazur_isomorphism

section exp_mapping

local notation `↑ₐ` := algebra_map 𝕜 A

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜` maps the spectrum of `a` into the spectrum of `exp 𝕜 a`. -/
theorem exp_mem_exp [is_R_or_C 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
  (a : A) {z : 𝕜} (hz : z ∈ spectrum 𝕜 a) : exp 𝕜 z ∈ spectrum 𝕜 (exp 𝕜 a) :=
begin
  have hexpmul : exp 𝕜 a = exp 𝕜 (a - ↑ₐ z) * ↑ₐ (exp 𝕜 z),
  { rw [algebra_map_exp_comm z, ←exp_add_of_commute (algebra.commutes z (a - ↑ₐz)).symm,
      sub_add_cancel] },
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐz) ^ n,
  have hb : summable (λ n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐz) ^ n),
  { refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial ∥a - ↑ₐz∥) _,
    filter_upwards [filter.eventually_cofinite_ne 0] with n hn,
    rw [norm_smul, mul_comm, norm_inv, is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat,
      ←div_eq_mul_inv],
    exact div_le_div (pow_nonneg (norm_nonneg _) n) (norm_pow_le' (a - ↑ₐz) (zero_lt_iff.mpr hn))
      (by exact_mod_cast nat.factorial_pos n)
      (by exact_mod_cast nat.factorial_le (lt_add_one n).le) },
  have h₀ : ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐz) ^ (n + 1) = (a - ↑ₐz) * b,
    { simpa only [mul_smul_comm, pow_succ] using hb.tsum_mul_left (a - ↑ₐz) },
  have h₁ : ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐz) ^ (n + 1) = b * (a - ↑ₐz),
    { simpa only [pow_succ', algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐz) },
  have h₃ : exp 𝕜 (a - ↑ₐz) = 1 + (a - ↑ₐz) * b,
  { rw exp_eq_tsum,
    convert tsum_eq_zero_add (exp_series_summable' (a - ↑ₐz)),
    simp only [nat.factorial_zero, nat.cast_one, inv_one, pow_zero, one_smul],
    exact h₀.symm },
  rw [spectrum.mem_iff, is_unit.sub_iff, ←one_mul (↑ₐ(exp 𝕜 z)), hexpmul, ←_root_.sub_mul,
    commute.is_unit_mul_iff (algebra.commutes (exp 𝕜 z) (exp 𝕜 (a - ↑ₐz) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, commute.is_unit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐz) * b = b * (a - ↑ₐz))],
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr is_unit.sub_iff).mp hz)),
end

end exp_mapping

end spectrum

namespace alg_hom

section normed_field
variables [nontrivially_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
local notation `↑ₐ` := algebra_map 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
instance : continuous_linear_map_class (A →ₐ[𝕜] 𝕜) 𝕜 A 𝕜 :=
{ map_continuous := λ φ, add_monoid_hom_class.continuous_of_bound φ ∥(1 : A)∥ $
    λ a, (mul_comm ∥a∥ ∥(1 : A)∥) ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ _),
  .. alg_hom_class.linear_map_class }

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
def to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
{ cont := map_continuous φ, .. φ.to_linear_map }

@[simp] lemma coe_to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) :
  ⇑φ.to_continuous_linear_map = φ := rfl

end normed_field

section nontrivially_normed_field
variables [nontrivially_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
local notation `↑ₐ` := algebra_map 𝕜 A

@[simp] lemma to_continuous_linear_map_norm [norm_one_class A] (φ : A →ₐ[𝕜] 𝕜) :
  ∥φ.to_continuous_linear_map∥ = 1 :=
continuous_linear_map.op_norm_eq_of_bounds zero_le_one
  (λ a, (one_mul ∥a∥).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
  (λ _ _ h, by simpa only [coe_to_continuous_linear_map, map_one, norm_one, mul_one] using h 1)

end nontrivially_normed_field

end alg_hom

namespace weak_dual

namespace character_space

variables [nontrivially_normed_field 𝕜] [normed_ring A] [complete_space A]
variables [normed_algebra 𝕜 A]

/-- The equivalence between characters and algebra homomorphisms into the base field. -/
def equiv_alg_hom : (character_space 𝕜 A) ≃ (A →ₐ[𝕜] 𝕜)  :=
{ to_fun := to_alg_hom,
  inv_fun := λ f,
  { val := f.to_continuous_linear_map,
    property := by { rw eq_set_map_one_map_mul, exact ⟨map_one f, map_mul f⟩ } },
  left_inv := λ f, subtype.ext $ continuous_linear_map.ext $ λ x, rfl,
  right_inv := λ f, alg_hom.ext $ λ x, rfl }

@[simp] lemma equiv_alg_hom_coe (f : character_space 𝕜 A) : ⇑(equiv_alg_hom f) = f := rfl

@[simp] lemma equiv_alg_hom_symm_coe  (f : A →ₐ[𝕜] 𝕜) : ⇑(equiv_alg_hom.symm f) = f := rfl

end character_space

end weak_dual
