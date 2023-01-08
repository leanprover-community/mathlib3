/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler
-/
import analysis.special_functions.complex.circle
import topology.instances.add_circle
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.group.integration
import measure_theory.integral.periodic
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`add_circle T = ℝ / ℤ • T`.

## Main definitions

* `haar_add_circle`, Haar measure on `add_circle T`, normalized to have total measure `1`. (Note
  that this is not the same normalisation as the standard measure defined in `integral.periodic`,
  so we do not declare it as a `measure_space` instance, to avoid confusion.)
* for `n : ℤ`, `fourier n` is the monomial `λ x, exp (2 π i n x / T)`, bundled as a continuous map
  from `add_circle T` to `ℂ`.
* `fourier_basis` is the Hilbert basis of `Lp ℂ 2 haar_add_circle` given by the images of the
  monomials `fourier n`.
* `fourier_coeff f n`, for `f : add_circle T → ℂ`, is the `n`-th Fourier coefficient of `f`
  (defined as an integral over `add_circle T`).

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(add_circle T, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourier_Lp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `add_circle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourier_basis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`has_sum_fourier_series_L2`). Parseval's identity, `tsum_sq_fourier_coeff`, is
a direct consequence.

For continuous maps `f : add_circle T → ℂ`, the theorem
`continuous_map.has_sum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i:ℤ), f.fourier_coeff i * fourier i`
converges to `f` in the uniform-convergence topology of `C(add_circle T, ℂ)`.
-/

noncomputable theory
open_locale ennreal complex_conjugate real
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

variables {T : ℝ}

namespace add_circle

/-! ### Map from `add_circle` to `circle` -/

lemma scaled_exp_map_periodic :
  function.periodic (λ x, exp_map_circle (2 * π / T * x)) T :=
begin
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with rfl | hT,
  { intro x, simp },
  { intro x, simp_rw mul_add, rw [div_mul_cancel _ hT, periodic_exp_map_circle] }
end

/-- The canonical map `λ x, exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
def to_circle : add_circle T → circle := (@scaled_exp_map_periodic T).lift

lemma to_circle_add (x : add_circle T) (y : add_circle T) :
  to_circle (x + y) = to_circle x * to_circle y :=
begin
  induction x using quotient_add_group.induction_on',
  induction y using quotient_add_group.induction_on',
  simp_rw [←quotient_add_group.coe_add, to_circle, function.periodic.lift_coe,
    mul_add, exp_map_circle_add],
end

lemma continuous_to_circle : continuous (@to_circle T) :=
continuous_coinduced_dom.mpr (exp_map_circle.continuous.comp $ continuous_const.mul continuous_id')

lemma injective_to_circle (hT : T ≠ 0) : function.injective (@to_circle T) :=
begin
  intros a b h,
  induction a using quotient_add_group.induction_on',
  induction b using quotient_add_group.induction_on',
  simp_rw [to_circle, function.periodic.lift_coe] at h,
  obtain ⟨m, hm⟩ := exp_map_circle_eq_exp_map_circle.mp h.symm,
  simp_rw [quotient_add_group.eq, add_subgroup.mem_zmultiples_iff, zsmul_eq_mul],
  use m,
  field_simp [real.two_pi_pos.ne'] at hm,
  rw ← mul_right_inj' real.two_pi_pos.ne',
  linarith
end

/-! ### Measure on `add_circle T`

In this file we use the Haar measure on `add_circle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `topology.instances.add_circle`). -/

variables [hT : fact (0 < T)]
include hT

/-- Haar measure on the additive circle, normalised to have total measure 1. -/
@[derive is_add_haar_measure]
def haar_add_circle : measure (add_circle T) := add_haar_measure ⊤

instance : is_probability_measure (@haar_add_circle T _) :=
  is_probability_measure.mk add_haar_measure_self

lemma volume_eq_smul_haar_add_circle :
  (volume : measure (add_circle T)) = ennreal.of_real T • haar_add_circle := rfl

end add_circle

open add_circle

section monomials

/-- The family of exponential monomials `λ x, exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
def fourier (n : ℤ) : C(add_circle T, ℂ) :=
{ to_fun := λ x, to_circle (n • x),
  continuous_to_fun := continuous_induced_dom.comp $ continuous_to_circle.comp $ continuous_zsmul _}

@[simp] lemma fourier_apply {n : ℤ} {x : add_circle T} : fourier n x = to_circle (n • x) := rfl

@[simp] lemma fourier_coe_apply {n : ℤ} {x : ℝ} :
  fourier n (x : add_circle T) = complex.exp (2 * π * complex.I * n * x / T) :=
begin
  rw [fourier_apply, ←quotient_add_group.coe_zsmul, to_circle, function.periodic.lift_coe,
    exp_map_circle_apply, complex.of_real_mul, complex.of_real_div, complex.of_real_mul,
    zsmul_eq_mul, complex.of_real_mul, complex.of_real_int_cast, complex.of_real_bit0,
    complex.of_real_one],
  congr' 1, ring,
end

@[simp] lemma fourier_zero {x : add_circle T} : fourier 0 x = 1 :=
begin
  induction x using quotient_add_group.induction_on',
  simp only [fourier_coe_apply, algebra_map.coe_zero, mul_zero, zero_mul,
    zero_div, complex.exp_zero],
end

@[simp] lemma fourier_eval_zero (n : ℤ) : fourier n (0 : add_circle T) = 1 :=
by rw [←quotient_add_group.coe_zero, fourier_coe_apply, complex.of_real_zero,
  mul_zero, zero_div, complex.exp_zero]

@[simp] lemma fourier_one {x : add_circle T} : fourier 1 x = to_circle x :=
by rw [fourier_apply, one_zsmul]

@[simp] lemma fourier_neg {n : ℤ} {x : add_circle T} : fourier (-n) x = conj (fourier n x) :=
begin
  induction x using quotient_add_group.induction_on',
  simp_rw [fourier_apply, to_circle, ←quotient_add_group.coe_zsmul,
    function.periodic.lift_coe, ←coe_inv_circle_eq_conj, ←exp_map_circle_neg, neg_smul, mul_neg],
end

@[simp] lemma fourier_add {m n : ℤ} {x : add_circle T} :
  fourier (m + n) x = fourier m x * fourier n x :=
by simp_rw [fourier_apply, add_zsmul, to_circle_add, coe_mul_unit_sphere]

lemma fourier_norm [fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 :=
begin
  rw continuous_map.norm_eq_supr_norm,
  have : ∀ (x : add_circle T), ‖fourier n x‖ = 1 := λ x, abs_coe_circle _,
  simp_rw this,
  exact @csupr_const _ _ _ has_zero.nonempty _,
end

/-- For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : add_circle T) :
  fourier n (x + ((T / 2 / n) : ℝ)) = - fourier n x :=
begin
  rw [fourier_apply, zsmul_add, ←quotient_add_group.coe_zsmul, to_circle_add, coe_mul_unit_sphere],
  have : (n : ℂ) ≠ 0 := by simpa using hn,
  have : ((@to_circle T ((n • (T / 2 / n)) : ℝ)) : ℂ) = -1,
  { rw [zsmul_eq_mul, to_circle, function.periodic.lift_coe, exp_map_circle_apply],
    replace hT := complex.of_real_ne_zero.mpr hT.ne',
    convert complex.exp_pi_mul_I using 3,
    field_simp, ring, },
  rw this, simp,
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` . -/
def fourier_subalgebra : subalgebra ℂ C(add_circle T, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is in fact the
linear span of these functions. -/
lemma fourier_subalgebra_coe : (@fourier_subalgebra T).to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, _⟩,
  { rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
    refine ⟨m + n, _⟩,
    ext1 z,
    exact fourier_add },
  { ext1 z, exact fourier_zero }
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is invariant under
complex conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra ((@fourier_subalgebra T).restrict_scalars ℝ) :=
begin
  apply subalgebra_conj_invariant,
  rintros _ ⟨n, rfl⟩,
  exact ⟨-n, ext (λ _, fourier_neg)⟩
end

variables [hT : fact (0 < T)]
include hT

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points. -/
lemma fourier_subalgebra_separates_points : (@fourier_subalgebra T).separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, _⟩,
  dsimp only, rw [fourier_one, fourier_one],
  contrapose! hxy,
  rw subtype.coe_inj at hxy,
  exact injective_to_circle hT.elim.ne' hxy,
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : (@fourier_subalgebra T).topological_closure = ⊤ :=
continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
  fourier_subalgebra fourier_subalgebra_separates_points fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `fourier n` is dense in `C(add_circle T, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range $ @fourier T)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `fourier n`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions `add_circle T → ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haar_add_circle T hT) :=
to_Lp p haar_add_circle ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  (@fourier_Lp T hT p _ n) =ᵐ[haar_add_circle] fourier n := coe_fn_to_Lp haar_add_circle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (@fourier_Lp T _ p _))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp (@haar_add_circle T hT) ℂ
    ).topological_closure_map_submodule (span_fourier_closure_eq_top),
  rw [map_span, range_comp],
  simp only [continuous_linear_map.coe_coe],
end

/-- The monomials `fourier n` are an orthonormal set with respect to normalised Haar measure. -/
lemma orthonormal_fourier : orthonormal ℂ (@fourier_Lp T _ 2 _) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp (@haar_add_circle T hT) (fourier i) (fourier j),
  simp_rw [←fourier_neg, ←fourier_add],
  split_ifs,
  { simp_rw [h, neg_add_self],
    have : ⇑(@fourier T 0) = (λ x, 1 : (add_circle T) → ℂ),
    { ext1, exact fourier_zero },
    rw [this, integral_const, measure_univ, ennreal.one_to_real, complex.real_smul,
      complex.of_real_one, mul_one] },
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  convert integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hij hT.elim),
  exact is_add_left_invariant.is_add_right_invariant
end

end monomials

section scope_hT -- everything from here on needs `0 < T`
variables [hT : fact (0 < T)]
include hT


section fourier_coeff
variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]

/-- The `n`-th Fourier coefficient of a function `add_circle T → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `add_circle T` of `fourier (-n) t • f t`. -/
def fourier_coeff (f : add_circle T → E) (n : ℤ) : E :=
∫ (t : add_circle T), fourier (-n) t • f t ∂ haar_add_circle

/-- The Fourier coefficients of a function can be computed as an integral
over `[a, a + T]` for any real `a`. -/
lemma fourier_coeff_eq_interval_integral (f : add_circle T → E) (n : ℤ) (a : ℝ) :
  fourier_coeff f n = (1 / T) • ∫ x in a .. a + T, @fourier T (-n) x • f x :=
begin
  have : ∀ (x : ℝ), @fourier T (-n) x • f x = (λ (z : add_circle T), @fourier T (-n) z • f z) x,
  { intro x, refl, },
  simp_rw this,
  rw [fourier_coeff, add_circle.interval_integral_preimage T a,
    volume_eq_smul_haar_add_circle, integral_smul_measure, ennreal.to_real_of_real hT.out.le,
    ←smul_assoc, smul_eq_mul, one_div_mul_cancel hT.out.ne', one_smul],
end

end fourier_coeff

section fourier_L2

/-- We define `fourier_basis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_add_circle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haar_add_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourier_basis : hilbert_basis ℤ ℂ (Lp ℂ 2 $ @haar_add_circle T hT) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge

/-- The elements of the Hilbert basis `fourier_basis` are the functions `fourier_Lp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp] lemma coe_fourier_basis : ⇑(@fourier_basis _ hT) = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_basis` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is `fourier_coeff f i`, i.e., the integral over `add_circle T` of `λ t, fourier (-i) t * f t`. -/
lemma fourier_basis_repr (f : Lp ℂ 2 $ @haar_add_circle T hT) (i : ℤ) :
  fourier_basis.repr f i = fourier_coeff f i :=
begin
  transitivity ∫ (t : add_circle T),
    conj (((@fourier_Lp T hT 2 _ i) : add_circle T → ℂ) t) * f t ∂ haar_add_circle,
  { simp [fourier_basis.repr_apply_apply f i, measure_theory.L2.inner_def] },
  { apply integral_congr_ae,
    filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
    rw [ht, ←fourier_neg, smul_eq_mul], }
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `add_circle T`. -/
lemma has_sum_fourier_series_L2 (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  has_sum (λ i, fourier_coeff f i • fourier_Lp 2 i) f :=
by { simp_rw ←fourier_basis_repr, simpa using hilbert_basis.has_sum_repr fourier_basis f }

/-- **Parseval's identity**: for an `L²` function `f` on `add_circle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
lemma tsum_sq_fourier_coeff (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  ∑' i : ℤ, ‖fourier_coeff f i‖ ^ 2 = ∫ (t : add_circle T), ‖f t‖ ^ 2 ∂ haar_add_circle :=
begin
  simp_rw ←fourier_basis_repr,
  have H₁ : ‖fourier_basis.repr f‖ ^ 2 = ∑' i, ‖fourier_basis.repr f i‖ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_basis.repr f),
    norm_num },
  have H₂ : ‖fourier_basis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def (add_circle T) ℂ ℂ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂, H₃], },
  { exact L2.integrable_inner f f },
end

end fourier_L2

section convergence

variables (f : C(add_circle T, ℂ))

lemma fourier_coeff_to_Lp (n : ℤ) :
  fourier_coeff (to_Lp 2 haar_add_circle ℂ f) n = fourier_coeff f n :=
integral_congr_ae (filter.eventually_eq.mul
  (filter.eventually_of_forall (by tauto))
  (continuous_map.coe_fn_to_ae_eq_fun haar_add_circle f))

variables {f}

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
lemma has_sum_fourier_series_of_summable (h : summable (fourier_coeff f)) :
  has_sum (λ i, fourier_coeff f i • fourier i) f :=
begin
  have sum_L2 := has_sum_fourier_series_L2 (to_Lp 2 haar_add_circle ℂ f),
  simp_rw fourier_coeff_to_Lp at sum_L2,
  refine continuous_map.has_sum_of_has_sum_Lp (summable_of_summable_norm _) sum_L2,
  simp_rw [norm_smul, fourier_norm, mul_one, summable_norm_iff],
  exact h,
end

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series of `f`
converges everywhere pointwise to `f`. -/
lemma has_pointwise_sum_fourier_series_of_summable
  (h : summable (fourier_coeff f)) (x : add_circle T) :
  has_sum (λ i, fourier_coeff f i • fourier i x) (f x) :=
(continuous_map.eval_clm ℂ x).has_sum (has_sum_fourier_series_of_summable h)

end convergence

end scope_hT
