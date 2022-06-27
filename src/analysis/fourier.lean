/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.measure.haar
import measure_theory.group.integration
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the circle

This file contains basic results on Fourier series.

## Main definitions

* `haar_circle`, Haar measure on the circle, normalized to have total measure `1`
* instances `measure_space`, `is_probability_measure` for the circle with respect to this measure
* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_circle`, via the embedding
  `continuous_map.to_Lp`
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`
  induced by taking Fourier series

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from
the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in `Lp ℂ p haar_circle`, i.e. that its `submodule.topological_closure` is
`⊤`.  This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal
set (in the L² space of the circle).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale real ennreal complex_conjugate classical
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

/-! ### Choice of measure on the circle -/

section haar_circle
/-! We make the circle into a measure space, using the Haar measure normalized to have total
measure 1. -/

local attribute [-instance] quotient.measurable_space

instance : topological_space real.angle := quotient.topological_space
instance : measurable_space real.angle := borel _
instance : borel_space real.angle := ⟨rfl⟩
instance : topological_add_group real.angle := topological_add_group_quotient _

example {G : Type*} [add_group G] (H : add_subgroup G) :
  (@add_action.orbit_rel H.opposite G _ _).r = (quotient_add_group.left_rel H).r :=
begin
  ext i j,
  change _ ∈ set.range _ ↔ _ ∈ H,
  split,
  { rintros ⟨h, rfl⟩,
    convert H.neg_mem h.prop,
    change  - (_ + _) + _ = _,
    simp only [add_submonoid.coe_subtype, neg_add_rev, neg_add_cancel_right, neg_inj],
    refl },
  { intros h,
    use ⟨_, H.neg_mem h⟩,
    change j + (-_) = _,
    simp }
  -- cases,

end
-- instance : t2_space real.angle :=
-- begin
--   have :
--   -- have := @t2_space_of_properly_discontinuous_vadd_of_t2_space (add_subgroup.zmultiples (2 * π)) _ ℝ _ _ _,
-- end

#exit

-- move this
lemma foo {α β : Type*} [topological_space α] [topological_space β] (s : set α) (hs : is_compact s)
  {f : α → β} (hf : continuous f) (hf' : set.surj_on f s set.univ) :
  compact_space β :=
{ compact_univ := begin
    convert hs.image hf,
    symmetry,
    rw eq_univ_iff_forall,
    intros x,
    exact hf' (mem_univ x)
  end }

-- move this
lemma baz : surj_on (coe : ℝ → real.angle) (Ioc 0 (2 * π)) univ :=
begin
  intros x _,
  apply real.angle.induction_on x,
  intros x₀,
  have : 0 < 2 * π := sorry,
  obtain ⟨k, ⟨hk₁, hk₂⟩, -⟩ := exists_unique_zsmul_near_of_pos' this x₀,
  sorry
  -- refine ⟨x₀, _⟩,
end

instance : compact_space real.angle :=
foo (Icc 0 (2 * π)) is_compact_Icc continuous_quotient_mk
  (baz.mono Ioc_subset_Icc_self (set.subset.refl _))

instance : normal_space real.angle := normal_of_compact_t2

/-- Haar measure on the circle, normalized to have total measure 1. -/
@[derive is_add_haar_measure]
def haar_circle : measure real.angle := add_haar_measure ⊤

instance : is_probability_measure haar_circle := ⟨add_haar_measure_self⟩

instance : regular haar_circle := measure_theory.measure.regular_add_haar_measure

instance : measure_space real.angle :=
{ volume := haar_circle,
  .. real.angle.measurable_space }

end haar_circle

/-! ### Monomials on the circle -/

section monomials

-- move this
lemma real.exp_mul_I_antiperiodic :
  function.antiperiodic (λ (x : ℝ), complex.exp (x * complex.I)) π :=
sorry

-- move this
lemma real.exp_mul_I_periodic :
  function.periodic (λ (x : ℝ), complex.exp (x * complex.I)) (2 * π) :=
real.exp_mul_I_antiperiodic.periodic

-- move this
lemma real.exp_mul_I_injective : function.injective real.exp_mul_I_periodic.lift :=
begin
  intros x,
  apply real.angle.induction_on x,
  intros x₀ y,
  apply real.angle.induction_on y,
  intros y₀ hxy₀,
  rw real.angle.angle_eq_iff_two_pi_dvd_sub,
  obtain ⟨n, hn⟩ := complex.exp_eq_exp_iff_exists_int.mp hxy₀,
  have : (x₀:ℂ) - y₀ = 2 * π * n,
  { linear_combination - complex.I * hn + (x₀ - y₀ - 2 * π * n) * complex.I_mul_I },
  exact ⟨n, by exact_mod_cast this⟩,
end

-- move this
lemma function.periodic.repeat {α β : Type*} [division_ring α] {c : α} {f : α → β}
  (hf : function.periodic f c) (n : ℤ) :
  function.periodic (λ t, f (n • t)) c :=
begin
  by_cases hn : (n:α) = 0,
  { intros x,
    simp [hn] },
  convert (hf.const_inv_smul₀ (n:α)⁻¹).int_mul n,
  { ext x,
    simp },
  { simp [mul_inv_cancel_left₀ hn] },
end

/-- The family of maps `λ t, exp (n * t * I)`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `real.angle` to `ℂ`. -/
def fourier (n : ℤ) : C(real.angle, ℂ) :=
{ to_fun := (real.exp_mul_I_periodic.repeat n).lift,
  continuous_to_fun := sorry }

@[simp] lemma fourier_apply (n : ℤ) (t : ℝ) : fourier n t = complex.exp (n * t * complex.I) :=
by simp [fourier]

@[simp] lemma fourier_zero {t : real.angle} : fourier 0 t = 1 := sorry

@[simp] lemma fourier_neg {n : ℤ} {z : real.angle} : fourier (-n) z = conj (fourier n z) :=
sorry

@[simp] lemma fourier_add {m n : ℤ} {z : real.angle} :
  fourier (m + n) z = (fourier m z) * (fourier n z) :=
sorry

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (n * t * I)` for `n ∈ ℤ`. -/
def fourier_subalgebra : subalgebra ℂ C(real.angle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (n * t * I)` for `n ∈ ℤ` is in fact the
linear span of these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  refine submonoid.closure_induction hx (λ _, id) ⟨0, _⟩ _,
  { ext1 z,
    exact fourier_zero },
  rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨m + n, _⟩,
  ext1 z,
  exact fourier_add,
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (n * t * I)` for `n ∈ ℤ` separates
points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, _, rfl⟩, _⟩,
  { exact subset_adjoin ⟨1, rfl⟩ },
  { simpa [fourier] using real.exp_mul_I_injective.ne hxy }
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (n * t * I)` for `n ∈ ℤ` is invariant
under complex conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra (fourier_subalgebra.restrict_scalars ℝ) :=
begin
  rintros _ ⟨f, hf, rfl⟩,
  change _ ∈ fourier_subalgebra,
  change _ ∈ fourier_subalgebra at hf,
  apply adjoin_induction hf,
  { rintros _ ⟨n, rfl⟩,
    suffices : fourier (-n) ∈ fourier_subalgebra,
    { convert this,
      ext1,
      simp },
    exact subset_adjoin ⟨-n, rfl⟩ },
  { intros c,
    exact fourier_subalgebra.algebra_map_mem (conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (n * t * I)` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
  fourier_subalgebra
  fourier_subalgebra_separates_points
  fourier_subalgebra_conj_invariant

/-- The linear span of the functions `exp (n * t * I)` is dense in `C(real.angle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of functions `λ t, exp (n * t * I)`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions on `real.angle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p haar_circle :=
to_Lp p haar_circle ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  ⇑(fourier_Lp p n) =ᵐ[haar_circle] fourier n :=
coe_fn_to_Lp haar_circle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the functions `exp (n * t * I)` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp haar_circle ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- For `n ≠ 0`, adding `n⁻¹ * π` negates the function `exp (n * t * I)`. -/
lemma fourier_antiperiodic {n : ℤ} (hn : n ≠ 0) :
  function.antiperiodic (fourier n) (↑((n:ℝ)⁻¹ * π) : real.angle) :=
sorry -- abstract nonsense


  -- fourier n ((↑((n:ℝ)⁻¹ * π) : real.angle) + t) = - fourier n t :=
-- begin
--   apply real.angle.induction_on t,
--   intros t₀,
--   calc _ = fourier n (↑((n:ℝ)⁻¹ * π + t₀) : real.angle) : by simp
--   ... = _ : _,
--   simp only [fourier_apply],
--   have : ↑n * ((↑n)⁻¹ * ↑real.pi * complex.I) = ↑real.pi * complex.I,
--   { have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
--     field_simp,
--     ring },
--   simp [mul_zpow, ← complex.exp_int_mul, complex.exp_pi_mul_I, this],
--   sorry
-- end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on the circle. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp haar_circle (fourier i) (fourier j),
  split_ifs,
  { simp [h, is_probability_measure.measure_univ, ← fourier_neg, ← fourier_add] },
  simp only [← fourier_add, ← fourier_neg],
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  have : ∀ t, fourier (-i+j) ((↑((↑(-i+j):ℝ)⁻¹ * π) : real.angle) + t) = - fourier (-i+j) t,
  { intros t,
    convert fourier_antiperiodic hij t using 2,
    abel },
  exact integral_eq_zero_of_add_left_eq_neg this,
end

end monomials

section fourier

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_circle`, which by
definition is an isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2 haar_circle) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num))

/-- The elements of the Hilbert basis `fourier_series` for `Lp ℂ 2 haar_circle` are the functions
`fourier_Lp 2`, the monomials `λ z, z ^ n` on the circle considered as elements of `L2`. -/
@[simp] lemma coe_fourier_series : ⇑fourier_series = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over the circle of `λ t, t ^ (-i) * f t`. -/
lemma fourier_series_repr (f : Lp ℂ 2 haar_circle) (i : ℤ) :
  fourier_series.repr f i = ∫ t : real.angle, fourier (-i) t * f t ∂ haar_circle :=
begin
  transitivity ∫ t : real.angle, conj ((fourier_Lp 2 i : real.angle → ℂ) t) * f t ∂ haar_circle,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  apply integral_congr_ae,
  filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
  rw [ht, ← fourier_neg],
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L2` topology on the circle. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 haar_circle) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: the sum of the squared norms of the Fourier coefficients equals the
`L2` norm of the function. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 haar_circle) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ t : real.angle, ∥f t∥ ^ 2 ∂ haar_circle :=
begin
  have H₁ : ∥fourier_series.repr f∥ ^ 2 = ∑' i, ∥fourier_series.repr f i∥ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f),
    norm_num },
  have H₂ : ∥fourier_series.repr f∥ ^ 2 = ∥f∥ ^2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def real.angle ℂ ℂ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂],
    exact H₃ },
  { exact L2.integrable_inner f f },
end

end fourier
