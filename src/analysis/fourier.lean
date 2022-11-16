/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.complex.circle
import analysis.special_functions.complex.circle
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.measure.haar
import measure_theory.measure.lebesgue
import measure_theory.group.integration
import measure_theory.integral.periodic
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series.

## Main definitions

* `haar_circle`, Haar measure on the group of angles `real.angle := ℝ / 2 π ℤ`,
  normalized to have total measure `1`.
* instances `measure_space`, `is_probability_measure` for `ℝ / 2 π ℤ`  with respect to this measure.
* for `n : ℤ`, `fourier n` is the monomial `λ θ, exp (i n θ)`, bundled as a continuous map from
  `real.angle` to `ℂ`.
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_circle`, via the embedding
  `continuous_map.to_Lp`
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`
  induced by taking Fourier series

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(real.angle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation,
and separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in the Lᵖ space of `real.angle`, i.e. that its `submodule.topological_closure`
is `⊤`. This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal set
(in the L² space of `real.angle`).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale ennreal complex_conjugate classical real
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

namespace real.angle

section angle_lemmas

/-! ### Lemmas about the exponential map -/

/-- These lemmas should eventually move to `special_functions.complex.circle` -/

lemma continuous_exp_map_circle : continuous exp_map_circle :=
  continuous_coinduced_dom.mpr _root_.exp_map_circle.continuous

lemma injective_exp_map_circle : function.injective exp_map_circle :=
begin
  intros a b h, rw [←arg_exp_map_circle a, ←arg_exp_map_circle b, h],
end

@[simp] lemma exp_map_circle_zsmul (n : ℤ) (θ : real.angle) :
  exp_map_circle (n • θ) = (exp_map_circle θ) ^ n :=
begin
  induction θ using real.angle.induction_on,
  exact exp_map_circle_hom.map_zsmul θ n,
end

/-! ### Properties of `real.angle` -/

instance : compact_space real.angle :=
begin
  haveI : fact (0 < 2 * π) := ⟨real.two_pi_pos⟩,
  apply add_circle.compact_space,
end


/-- This is a little silly, since the standard measure on `add_circle T` is defined to be
`T` times the normalised Haar measure, and we're just dividing out the constant again.  --/
instance : measure_space real.angle :=
begin
  haveI : fact (0 < 2 * π) := ⟨real.two_pi_pos⟩,
  exact { volume := (ennreal.of_real (1 / (2 * π))) • (add_circle.measure_space _).volume }
end

instance : is_probability_measure (volume : measure real.angle) :=
begin
  apply is_probability_measure.mk,
  dsimp [(volume)],
  rw [←mul_assoc, ←ennreal.of_real_mul' real.two_pi_pos.le, div_mul_cancel _ real.two_pi_pos.ne',
    ennreal.of_real_one, one_mul],
  exact add_haar_measure_self,
end

instance : measurable_space real.angle := add_circle.measurable_space
instance : borel_space      real.angle := add_circle.borel_space

end angle_lemmas

section monomials

/-- The family of exponential monomials `λ θ, exp (i n θ)`, parametrized by `n : ℤ` and considered
as bundled continuous maps from `real.angle` to `ℂ`. -/
def fourier (n : ℤ) : C(real.angle, ℂ) :=
{ to_fun := λ θ, exp_map_circle (n • θ),
  continuous_to_fun := (continuous_induced_dom.comp $ continuous_exp_map_circle.comp $
  continuous_zsmul _) }

@[simp] lemma fourier_zero {θ : real.angle} : fourier 0 θ = 1 :=
begin
  simp only [fourier, zero_smul, continuous_map.coe_mk, exp_map_circle_zero, coe_one_unit_sphere]
end

@[simp] lemma fourier_one {θ : real.angle} : fourier 1 θ = exp_map_circle θ :=
begin
  simp only [fourier, one_zsmul, continuous_map.coe_mk],
end

@[simp] lemma fourier_neg {n : ℤ} {z : real.angle} : fourier (-n) z = conj (fourier n z) :=
begin
  rw [fourier, fourier, continuous_map.coe_mk, continuous_map.coe_mk,
  neg_zsmul, exp_map_circle_neg, ←coe_inv_circle_eq_conj],
end

@[simp] lemma fourier_add {m n : ℤ} {z : real.angle} :
  fourier (m + n) z = (fourier m z) * (fourier n z) :=
begin
  simp_rw [fourier, continuous_map.coe_mk, add_zsmul, exp_map_circle_add,
    coe_mul_unit_sphere],
end

lemma fourier_eq_pow (n : ℤ) (θ : real.angle) : fourier n θ = (exp_map_circle θ) ^ n :=
begin
  simp_rw [fourier, continuous_map.coe_mk, exp_map_circle_zsmul, coe_zpow_unit_sphere],
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (i n θ)` for `n ∈ ℤ`. -/
def fourier_subalgebra : subalgebra ℂ C(real.angle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(real.angle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is in fact the linear
span of these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, _⟩,
  { rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
    refine ⟨m + n, _⟩,
    ext1 z,
    exact fourier_add },
  { ext1 θ, exact fourier_zero }
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (i n θ)` for `n ∈ ℤ` separates points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, _⟩,
  dsimp, rw [fourier_one, fourier_one, subtype.coe_inj],
  contrapose! hxy,
  exact injective_exp_map_circle hxy,
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (i n θ)` for `n ∈ ℤ` is invariant
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
  { exact λ c, fourier_subalgebra.algebra_map_mem (conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(real.angle, ℂ)` generated by `exp (i n θ)` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
  fourier_subalgebra fourier_subalgebra_separates_points fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `exp (i n θ)` is dense in `C(real.angle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `exp (i n θ)`, parametrized by `n : ℤ` and considered as elements of
the `Lp` space of functions on `real.angle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p :=
to_Lp p volume ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  ⇑(fourier_Lp p n) =ᵐ[volume] fourier n := coe_fn_to_Lp volume (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `exp (i n θ)` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp volume ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- For `n ≠ 0`, a translation by `π / n` negates the function `exp (i n θ)`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (θ : real.angle) :
  fourier n (θ + ((π / n) : ℝ)) = - fourier n θ :=
begin
  simp_rw fourier_eq_pow,
  rw [exp_map_circle_add, ←coe_zpow_unit_sphere, mul_zpow, coe_mul_unit_sphere],
  suffices : ((((exp_map_circle ((π / n) : ℝ)) ^ n) : circle) : ℂ) = -1,
  { rw this, simp only [coe_zpow_unit_sphere, mul_neg, mul_one] },
  rw [←exp_map_circle_zsmul, ←coe_zsmul, zsmul_eq_mul,
    mul_div_cancel', exp_map_circle_coe, exp_map_circle_apply],
  apply complex.exp_pi_mul_I,
  simpa using hn,
end

/-- The monomials `exp (i n θ)` are an orthonormal set with respect to Haar measure. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp volume (fourier i) (fourier j),
  simp_rw [←fourier_neg, ←fourier_add],
  split_ifs,
  { simp_rw [h, neg_add_self],
    have : ⇑(fourier 0) = (λ x, 1 : real.angle → ℂ),
    { ext1, exact fourier_zero },
    rw [this, integral_const, measure_univ, ennreal.one_to_real, complex.real_smul,
      complex.of_real_one, mul_one] },
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hij),
end

end monomials

section fourier

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 volume`, which by
definition is an isometric isomorphism from `Lp ℂ 2 volume` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge

/-- The elements of the Hilbert basis `fourier_series` are the functions `fourier_Lp 2`, i.e. the
monomials `exp (i n θ)` on the circle considered as elements of `L2`. -/
@[simp] lemma coe_fourier_series : ⇑fourier_series = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over `ℝ / 2 π ℤ` of `λ t, fourier (-i) t * f t`. -/
lemma fourier_series_repr (f : Lp ℂ 2 volume) (i : ℤ) :
  fourier_series.repr f i = ∫ t : real.angle, fourier (-i) t * f t :=
begin
  transitivity ∫ t : real.angle, conj ((fourier_Lp 2 i : real.angle → ℂ) t) * f t,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  apply integral_congr_ae,
  filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
  rw [ht, ← fourier_neg],
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L2` space of `ℝ / 2 π ℤ`. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 volume) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: for a function `f` on `ℝ / 2 π ℤ`, the sum of the squared norms of the
Fourier coefficients equals the `L2` norm of the function. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 volume) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ (t : real.angle), ∥f t∥ ^ 2 :=
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

end real.angle
