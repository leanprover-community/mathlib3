/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.spectrum
import analysis.special_functions.pow
import analysis.complex.liouville
import analysis.analytic.radius_liminf
/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius : ℝ≥0∞`: supremum of `∥k∥₊` for all `k ∈ spectrum 𝕜 a`

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

* after we have Liouville's theorem, prove that the spectrum is nonempty when the
  scalar field is ℂ.
* compute all derivatives of `resolvent a`.

-/

open_locale ennreal

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

variables [normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A]

local notation `σ` := spectrum 𝕜
local notation `ρ` := resolvent_set 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

lemma mem_resolvent_set_of_spectral_radius_lt {a : A} {k : 𝕜} (h : spectral_radius 𝕜 a < ∥k∥₊) :
  k ∈ ρ a :=
not_not.mp (λ hn, (lt_self_iff_false _).mp (lt_of_le_of_lt (le_bsupr k hn) h))

variable [complete_space A]

lemma is_open_resolvent_set (a : A) : is_open (ρ a) :=
units.is_open.preimage ((algebra_map_isometry 𝕜 A).continuous.sub continuous_const)

lemma is_closed (a : A) : is_closed (σ a) :=
(is_open_resolvent_set a).is_closed_compl

lemma mem_resolvent_of_norm_lt {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) :
  k ∈ ρ a :=
begin
  rw [resolvent_set, set.mem_set_of_eq, algebra.algebra_map_eq_smul_one],
  have hk : k ≠ 0 := ne_zero_of_norm_ne_zero (by linarith [norm_nonneg a]),
  let ku := units.map (↑ₐ).to_monoid_hom (units.mk0 k hk),
  have hku : ∥-a∥ < ∥(↑ku⁻¹:A)∥⁻¹ := by simpa [ku, algebra_map_isometry] using h,
  simpa [ku, sub_eq_add_neg, algebra.algebra_map_eq_smul_one] using (ku.add (-a) hku).is_unit,
end

lemma norm_le_norm_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) :
  ∥k∥ ≤ ∥a∥ :=
le_of_not_lt $ mt mem_resolvent_of_norm_lt hk

lemma subset_closed_ball_norm (a : A) :
  σ a ⊆ metric.closed_ball (0 : 𝕜) (∥a∥) :=
λ k hk, by simp [norm_le_norm_of_mem hk]

lemma is_bounded (a : A) : metric.bounded (σ a) :=
(metric.bounded_iff_subset_ball 0).mpr ⟨∥a∥, subset_closed_ball_norm a⟩

theorem is_compact [proper_space 𝕜] (a : A) : is_compact (σ a) :=
metric.is_compact_of_is_closed_bounded (is_closed a) (is_bounded a)

theorem spectral_radius_le_nnnorm (a : A) :
  spectral_radius 𝕜 a ≤ ∥a∥₊ :=
by { refine bsupr_le (λ k hk, _), exact_mod_cast norm_le_norm_of_mem hk }

open ennreal polynomial

variable (𝕜)
theorem spectral_radius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
  spectral_radius 𝕜 a ≤ ∥a ^ (n + 1)∥₊ ^ (1 / (n + 1) : ℝ) :=
begin
  refine bsupr_le (λ k hk, _),
  /- apply easy direction of the spectral mapping theorem for polynomials -/
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)),
    by simpa only [one_mul, algebra.algebra_map_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (monomial (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩,
  /- power of the norm is bounded by norm of the power -/
  have nnnorm_pow_le : (↑(∥k∥₊ ^ (n + 1)) : ℝ≥0∞) ≤ ↑∥a ^ (n + 1)∥₊,
    by simpa only [norm_to_nnreal, nnnorm_pow k (n+1)]
      using coe_mono (real.to_nnreal_mono (norm_le_norm_of_mem pow_mem)),
  /- take (n + 1)ᵗʰ roots and clean up the left-hand side -/
  have hn : 0 < ((n + 1) : ℝ), by exact_mod_cast nat.succ_pos',
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le,
  erw [coe_pow, ←rpow_nat_cast, ←rpow_mul, mul_one_div_cancel hn.ne', rpow_one],
end

end spectrum_compact

section resolvent

open filter asymptotics

variables [nondiscrete_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]

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
`is_O (resolvent a) (λ z, z⁻¹) (cobounded 𝕜)`. -/
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
  { rw [units.smul_def, norm_smul, units.coe_inv', norm_inv],
    calc ∥(z : 𝕜)∥⁻¹ * ∥a∥ ≤ δ * (∥a∥ + 1)⁻¹ * ∥a∥
        : mul_le_mul_of_nonneg_right (hz.trans (min_le_left _ _)) (norm_nonneg _)
    ...                   < δ
        : by { conv { rw mul_assoc, to_rhs, rw (mul_one δ).symm },
               exact mul_lt_mul_of_pos_left
                 ((inv_mul_lt_iff ha₁).mpr ((mul_one (∥a∥ + 1)).symm ▸ (lt_add_one _))) δ_pos } },
  rw [←inv_smul_smul z (resolvent a (z : 𝕜)), units_smul_resolvent_self, resolvent,
    algebra.algebra_map_eq_smul_one, one_smul, units.smul_def, norm_smul, units.coe_inv', norm_inv],
  calc _ ≤ ε * c⁻¹ * c : mul_le_mul (hz.trans (min_le_right _ _)) (hδ (mem_ball_zero_iff.mpr lt_δ))
                           (norm_nonneg _) (mul_pos hε (inv_pos.mpr c_pos)).le
  ...    = _           : inv_mul_cancel_right₀ c_pos.ne.symm ε,
end

end resolvent

section one_sub_smul

open continuous_multilinear_map ennreal formal_multilinear_series
open_locale nnreal ennreal

variables
[nondiscrete_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A]

variable (𝕜)
/-- In a Banach algebra `A` over a nondiscrete normed field `𝕜`, for any `a : A` the
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
      rwa [units.coe_inv', nnnorm_inv, coe_inv (nnnorm_ne_zero_iff.mpr
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

/- the assumption below that `A` be second countable is a technical limitation due to
the current implementation of Bochner integrals in mathlib. Once this is changed, we
will be able to remove that hypothesis. -/
variables
[normed_ring A] [normed_algebra ℂ A] [complete_space A]
[measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

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
begin
  refine tendsto_of_le_liminf_of_limsup_le _ _ (by apply_auto_param) (by apply_auto_param),
  { rw [←liminf_nat_add _ 1, liminf_eq_supr_infi_of_nat],
    refine le_trans _ (le_supr _ 0),
    exact le_binfi (λ i hi, spectral_radius_le_pow_nnnorm_pow_one_div ℂ a i) },
  { exact limsup_pow_nnnorm_pow_one_div_le_spectral_radius a },
end

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
  [nontrivial A] [topological_space.second_countable_topology A]
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

end spectrum

namespace alg_hom

section normed_field
variables [normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
local notation `↑ₐ` := algebra_map 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
@[simps] def to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
φ.to_linear_map.mk_continuous_of_exists_bound $
  ⟨1, λ a, (one_mul ∥a∥).symm ▸ spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)⟩

lemma continuous (φ : A →ₐ[𝕜] 𝕜) : continuous φ := φ.to_continuous_linear_map.continuous

end normed_field

section nondiscrete_normed_field
variables [nondiscrete_normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
local notation `↑ₐ` := algebra_map 𝕜 A

@[simp] lemma to_continuous_linear_map_norm [norm_one_class A] (φ : A →ₐ[𝕜] 𝕜) :
  ∥φ.to_continuous_linear_map∥ = 1 :=
continuous_linear_map.op_norm_eq_of_bounds zero_le_one
  (λ a, (one_mul ∥a∥).symm ▸ spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _))
  (λ _ _ h, by simpa only [to_continuous_linear_map_apply, mul_one, map_one, norm_one] using h 1)

end nondiscrete_normed_field

end alg_hom
