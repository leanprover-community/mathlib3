/-
Copyright (c) 2021-2 Heather Macbeth, David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
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
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_add_circle`, via the embedding
  `continuous_map.to_Lp`.
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_add_circle` to
  `ℓ²(ℤ, ℂ)` induced by taking Fourier coefficients.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(add_circle T, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation,
and separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in the Lᵖ space of `add_circle T`, i.e. that its
`submodule.topological_closure` is `⊤`. This follows from the previous theorem using general theory
on approximation of Lᵖ functions by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal set
(in the L² space of `add_circle T` with respect to `haar_add_circle`).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale ennreal complex_conjugate classical real
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

def to_circle := (@scaled_exp_map_periodic T).lift

lemma to_circle_zero : @to_circle T 0 = 1 :=
begin
  rw [←quotient_add_group.coe_zero, to_circle, function.periodic.lift_coe, mul_zero],
  exact exp_map_circle_zero,
end

lemma to_circle_add (x : add_circle T) (y : add_circle T) :
  to_circle (x + y) = to_circle x * to_circle y :=
begin
  induction x using quotient_add_group.induction_on',
  induction y using quotient_add_group.induction_on',
  simp_rw [←quotient_add_group.coe_add, to_circle, function.periodic.lift_coe,
    mul_add, exp_map_circle_add],
end

def to_circle_hom : add_circle T →+ (additive circle) :=
{ to_fun := additive.of_mul ∘ to_circle,
  map_zero' := to_circle_zero,
  map_add' := to_circle_add }

lemma to_circle_continuous : continuous (@to_circle T) :=
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
  have : ↑m * (2 * π) = (2 * π / T) * (m * T) := by { field_simp, ring },
  rw [this, ←mul_add, mul_eq_mul_left_iff] at hm,
  cases hm, { rw hm, ring, },
  { exfalso, refine div_ne_zero real.two_pi_pos.ne' hT hm },
end

end add_circle

section def_measure

/-! ### Measure on `add_circle T`

In this file we use the Haar measure on `add_circle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `topology.instances.add_circle`). -/

variables [hT : fact (0 < T)]
include hT

def haar_add_circle : measure (add_circle T) := add_haar_measure ⊤

instance : is_probability_measure (@haar_add_circle T _) :=
  is_probability_measure.mk add_haar_measure_self

end def_measure

section monomials

/-- The family of exponential monomials `λ x, exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
def fourier (n : ℤ) : C(add_circle T, ℂ) :=
{ to_fun := λ x, add_circle.to_circle (n • x),
  continuous_to_fun := continuous_induced_dom.comp $ add_circle.to_circle_continuous.comp $
  continuous_zsmul _ }

@[simp] lemma fourier_apply {n : ℤ} {x : add_circle T} :
  fourier n x = add_circle.to_circle (n • x) := rfl

@[simp] lemma fourier_zero {x : add_circle T} : fourier 0 x = 1 :=
by simp only [fourier_apply, zero_smul, add_circle.to_circle_zero, coe_one_unit_sphere]

lemma fourier_eq_pow (n : ℤ) (x : add_circle T) : fourier n x = (add_circle.to_circle x) ^ n :=
begin
  rw [fourier_apply, ←coe_zpow_unit_sphere, subtype.coe_inj],
  exact add_circle.to_circle_hom.map_zsmul x n,
end

@[simp] lemma fourier_one {x : add_circle T} : fourier 1 x = add_circle.to_circle x :=
by rw [fourier_apply, one_zsmul]

@[simp] lemma fourier_neg {n : ℤ} {x : add_circle T} : fourier (-n) x = conj (fourier n x) :=
by simp_rw [fourier_eq_pow, zpow_neg, ←coe_zpow_unit_sphere, ←coe_inv_circle_eq_conj,
  coe_inv_unit_sphere]

@[simp] lemma fourier_add {m n : ℤ} {x : add_circle T} :
  fourier (m + n) x = (fourier m x) * (fourier n x) :=
begin
  simp_rw [fourier, continuous_map.coe_mk, add_zsmul, add_circle.to_circle_add, coe_mul_unit_sphere]
end

/-- For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : add_circle T) :
  fourier n (x + ((T / 2 / n) : ℝ)) = - fourier n x :=
begin
  rw [fourier_apply, zsmul_add, ←quotient_add_group.coe_zsmul, add_circle.to_circle_add,
    coe_mul_unit_sphere],
  have : (n : ℂ) ≠ 0 := by simpa using hn,
  have : ((@add_circle.to_circle T ((n • (T / 2 / n)) : ℝ)) : ℂ) = -1,
  { rw [zsmul_eq_mul, add_circle.to_circle, function.periodic.lift_coe, exp_map_circle_apply],
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
  rintros _ ⟨n, rfl⟩, use -n,
  ext1 x, apply fourier_neg
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
  exact add_circle.injective_to_circle hT.elim.ne' hxy,
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
  ⇑(@fourier_Lp T hT p _ n) =ᵐ[haar_add_circle] fourier n :=
coe_fn_to_Lp haar_add_circle (fourier n)

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
  rw haar_add_circle,
  exact is_mul_left_invariant.is_add_right_invariant
end

end monomials

section fourier
variables [hT : fact (0 < T)]
include hT

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_add_circle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haar_add_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2 $ @haar_add_circle T hT) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge

/-- The elements of the Hilbert basis `fourier_series` are the functions `fourier_Lp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp] lemma coe_fourier_series : ⇑(@fourier_series _ hT) = fourier_Lp 2 :=
hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over `add_circle T` of `λ t, fourier (-i) t * f t`. -/
lemma fourier_series_repr (f : Lp ℂ 2 $ @haar_add_circle T hT) (i : ℤ) :
  fourier_series.repr f i = ∫ (t : add_circle T), fourier (-i) t * f t ∂ haar_add_circle :=
begin
  transitivity ∫ (t : add_circle T),
    conj (((@fourier_Lp T hT 2 _ i) : add_circle T → ℂ) t) * f t ∂ haar_add_circle,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  { apply integral_congr_ae,
    filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
    rw [ht, ←fourier_neg] }
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `add_circle T`. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: for an `L²` function `f` on `add_circle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ (t : add_circle T), ∥f t∥ ^ 2 ∂ haar_add_circle :=
begin
  have H₁ : ∥fourier_series.repr f∥ ^ 2 = ∑' i, ∥fourier_series.repr f i∥ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f),
    norm_num },
  have H₂ : ∥fourier_series.repr f∥ ^ 2 = ∥f∥ ^2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def (add_circle T) ℂ ℂ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂],
    exact H₃ },
  { exact L2.integrable_inner f f },
end

end fourier
