/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.complex.determinant
import data.complex.is_R_or_C

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `re_clm`
* `im_clm`
* `of_real_clm`
* `conj_cle`

They are bundled versions of the real part, the imaginary part, the embedding of `ℝ` in `ℂ`, and
the complex conjugate as continuous `ℝ`-linear maps. The last two are also bundled as linear
isometries in `of_real_li` and `conj_lie`.

We also register the fact that `ℂ` is an `is_R_or_C` field.
-/
noncomputable theory


namespace complex

open_locale complex_conjugate topological_space

instance : has_norm ℂ := ⟨abs⟩

@[simp] lemma norm_eq_abs (z : ℂ) : ∥z∥ = abs z := rfl

instance : normed_group ℂ :=
normed_group.of_core ℂ
{ norm_eq_zero_iff := λ z, abs_eq_zero,
  triangle := abs_add,
  norm_neg := abs_neg }

instance : normed_field ℂ :=
{ norm := abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := abs_mul,
  .. complex.field, .. complex.normed_group }

instance : nontrivially_normed_field ℂ :=
{ non_trivial := ⟨2, by simp; norm_num⟩ }

instance {R : Type*} [normed_field R] [normed_algebra R ℝ] : normed_algebra R ℂ :=
{ norm_smul_le := λ r x, begin
    rw [norm_eq_abs, norm_eq_abs, ←algebra_map_smul ℝ r x, algebra.smul_def, abs_mul,
      ←norm_algebra_map' ℝ r, coe_algebra_map, abs_of_real],
    refl,
  end,
  to_algebra := complex.algebra }

/-- The module structure from `module.complex_to_real` is a normed space. -/
@[priority 900] -- see Note [lower instance priority]
instance _root_.normed_space.complex_to_real {E : Type*} [normed_group E] [normed_space ℂ E] :
  normed_space ℝ E :=
normed_space.restrict_scalars ℝ ℂ E

lemma dist_eq (z w : ℂ) : dist z w = abs (z - w) := rfl

lemma dist_eq_re_im (z w : ℂ) : dist z w = real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) :=
by { rw [sq, sq], refl }

@[simp] lemma dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
  dist (mk x₁ y₁) (mk x₂ y₂) = real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
dist_eq_re_im _ _

lemma dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im :=
by rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, zero_add, real.sqrt_sq_eq_abs, real.dist_eq]

lemma nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
nnreal.eq $ dist_of_re_eq h

lemma edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im :=
by rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

lemma dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re :=
by rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, add_zero, real.sqrt_sq_eq_abs, real.dist_eq]

lemma nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
nnreal.eq $ dist_of_im_eq h

lemma edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re :=
by rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

lemma dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| :=
by rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, real.dist_eq, sub_neg_eq_add, ← two_mul,
  _root_.abs_mul, abs_of_pos (@two_pos ℝ _ _)]

lemma nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * real.nnabs z.im :=
nnreal.eq $ by rw [← dist_nndist, nnreal.coe_mul, nnreal.coe_two, real.coe_nnabs, dist_conj_self]

lemma dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| :=
by rw [dist_comm, dist_conj_self]

lemma nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * real.nnabs z.im :=
by rw [nndist_comm, nndist_conj_self]

@[simp] lemma comap_abs_nhds_zero : filter.comap abs (𝓝 0) = 𝓝 0 := comap_norm_nhds_zero

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = |(r : ℝ)| :=
by { rw ← of_real_rat_cast, exact norm_real _ }

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ∥(n : ℂ)∥ = |n| :=
by simp [← rat.cast_coe_int] {single_pass := tt}

lemma norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n :=
by simp [hn]

@[continuity] lemma continuous_abs : continuous abs := continuous_norm

@[continuity] lemma continuous_norm_sq : continuous norm_sq :=
by simpa [← norm_sq_eq_abs] using continuous_abs.pow 2

@[simp, norm_cast] lemma nnnorm_real (r : ℝ) : ∥(r : ℂ)∥₊ = ∥r∥₊ :=
subtype.ext $ norm_real r

@[simp, norm_cast] lemma nnnorm_nat (n : ℕ) : ∥(n : ℂ)∥₊ = n :=
subtype.ext $ by simp

@[simp, norm_cast] lemma nnnorm_int (n : ℤ) : ∥(n : ℂ)∥₊ = ∥n∥₊ :=
subtype.ext $ by simp only [coe_nnnorm, norm_int, int.norm_eq_abs]

lemma nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥₊ = 1 :=
begin
  refine (@pow_left_inj nnreal _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _,
  rw [←nnnorm_pow, h, nnnorm_one, one_pow],
end

lemma norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥ = 1 :=
congr_arg coe (nnnorm_eq_one_of_pow_eq_one h hn)

/-- The `abs` function on `ℂ` is proper. -/
lemma tendsto_abs_cocompact_at_top : filter.tendsto abs (filter.cocompact ℂ) filter.at_top :=
tendsto_norm_cocompact_at_top

/-- The `norm_sq` function on `ℂ` is proper. -/
lemma tendsto_norm_sq_cocompact_at_top :
  filter.tendsto norm_sq (filter.cocompact ℂ) filter.at_top :=
by simpa [mul_self_abs] using
  tendsto_abs_cocompact_at_top.at_top_mul_at_top tendsto_abs_cocompact_at_top

open continuous_linear_map

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_clm : ℂ →L[ℝ] ℝ := re_lm.mk_continuous 1 (λ x, by simp [abs_re_le_abs])

@[continuity] lemma continuous_re : continuous re := re_clm.continuous

@[simp] lemma re_clm_coe : (coe (re_clm) : ℂ →ₗ[ℝ] ℝ) = re_lm := rfl

@[simp] lemma re_clm_apply (z : ℂ) : (re_clm : ℂ → ℝ) z = z.re := rfl

@[simp] lemma re_clm_norm : ∥re_clm∥ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ∥re_clm 1∥ : by simp
   ... ≤ ∥re_clm∥ : unit_le_op_norm _ _ (by simp)

@[simp] lemma re_clm_nnnorm : ∥re_clm∥₊ = 1 := subtype.ext re_clm_norm

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def im_clm : ℂ →L[ℝ] ℝ := im_lm.mk_continuous 1 (λ x, by simp [abs_im_le_abs])

@[continuity] lemma continuous_im : continuous im := im_clm.continuous

@[simp] lemma im_clm_coe : (coe (im_clm) : ℂ →ₗ[ℝ] ℝ) = im_lm := rfl

@[simp] lemma im_clm_apply (z : ℂ) : (im_clm : ℂ → ℝ) z = z.im := rfl

@[simp] lemma im_clm_norm : ∥im_clm∥ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ∥im_clm I∥ : by simp
   ... ≤ ∥im_clm∥ : unit_le_op_norm _ _ (by simp)

@[simp] lemma im_clm_nnnorm : ∥im_clm∥₊ = 1 := subtype.ext im_clm_norm

lemma restrict_scalars_one_smul_right' {E : Type*} [normed_group E] [normed_space ℂ E] (x : E) :
  continuous_linear_map.restrict_scalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] E) =
    re_clm.smul_right x + I • im_clm.smul_right x :=
by { ext ⟨a, b⟩, simp [mk_eq_add_mul_I, add_smul, mul_smul, smul_comm I] }

lemma restrict_scalars_one_smul_right (x : ℂ) :
  continuous_linear_map.restrict_scalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] ℂ) = x • 1 :=
by { ext1 z, dsimp, apply mul_comm }

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conj_lie : ℂ ≃ₗᵢ[ℝ] ℂ := ⟨conj_ae.to_linear_equiv, abs_conj⟩

@[simp] lemma conj_lie_apply (z : ℂ) : conj_lie z = conj z := rfl

@[simp] lemma conj_lie_symm : conj_lie.symm = conj_lie := rfl

lemma isometry_conj : isometry (conj : ℂ → ℂ) := conj_lie.isometry

@[simp] lemma dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
isometry_conj.dist_eq z w

@[simp] lemma nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
isometry_conj.nndist_eq z w

lemma dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) :=
by rw [← dist_conj_conj, conj_conj]

lemma nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
subtype.ext $ dist_conj_comm _ _

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp] lemma det_conj_lie : (conj_lie.to_linear_equiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
det_conj_ae

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp] lemma linear_equiv_det_conj_lie : conj_lie.to_linear_equiv.det = -1 :=
linear_equiv_det_conj_ae

instance : has_continuous_star ℂ := ⟨conj_lie.continuous⟩

@[continuity] lemma continuous_conj : continuous (conj : ℂ → ℂ) := continuous_star

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conj_cle : ℂ ≃L[ℝ] ℂ := conj_lie

@[simp] lemma conj_cle_coe : conj_cle.to_linear_equiv = conj_ae.to_linear_equiv := rfl

@[simp] lemma conj_cle_apply (z : ℂ) : conj_cle z = conj z := rfl

@[simp] lemma conj_cle_norm : ∥(conj_cle : ℂ →L[ℝ] ℂ)∥ = 1 :=
conj_lie.to_linear_isometry.norm_to_continuous_linear_map

@[simp] lemma conj_cle_nnorm : ∥(conj_cle : ℂ →L[ℝ] ℂ)∥₊ = 1 := subtype.ext conj_cle_norm

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_li : ℝ →ₗᵢ[ℝ] ℂ := ⟨of_real_am.to_linear_map, norm_real⟩

lemma isometry_of_real : isometry (coe : ℝ → ℂ) := of_real_li.isometry

@[continuity] lemma continuous_of_real : continuous (coe : ℝ → ℂ) := of_real_li.continuous

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_clm : ℝ →L[ℝ] ℂ := of_real_li.to_continuous_linear_map

@[simp] lemma of_real_clm_coe : (of_real_clm : ℝ →ₗ[ℝ] ℂ) = of_real_am.to_linear_map := rfl

@[simp] lemma of_real_clm_apply (x : ℝ) : of_real_clm x = x := rfl

@[simp] lemma of_real_clm_norm : ∥of_real_clm∥ = 1 := of_real_li.norm_to_continuous_linear_map

@[simp] lemma of_real_clm_nnnorm : ∥of_real_clm∥₊ = 1 := subtype.ext $ of_real_clm_norm

noncomputable instance : is_R_or_C ℂ :=
{ re := ⟨complex.re, complex.zero_re, complex.add_re⟩,
  im := ⟨complex.im, complex.zero_im, complex.add_im⟩,
  I := complex.I,
  I_re_ax := by simp only [add_monoid_hom.coe_mk, complex.I_re],
  I_mul_I_ax := by simp only [complex.I_mul_I, eq_self_iff_true, or_true],
  re_add_im_ax := λ z, by simp only [add_monoid_hom.coe_mk, complex.re_add_im,
                                     complex.coe_algebra_map, complex.of_real_eq_coe],
  of_real_re_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_re,
                                      complex.coe_algebra_map, complex.of_real_eq_coe],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_im,
                                      complex.coe_algebra_map, complex.of_real_eq_coe],
  mul_re_ax := λ z w, by simp only [complex.mul_re, add_monoid_hom.coe_mk],
  mul_im_ax := λ z w, by simp only [add_monoid_hom.coe_mk, complex.mul_im],
  conj_re_ax := λ z, rfl,
  conj_im_ax := λ z, rfl,
  conj_I_ax := by simp only [complex.conj_I, ring_hom.coe_mk],
  norm_sq_eq_def_ax := λ z, by simp only [←complex.norm_sq_eq_abs, ←complex.norm_sq_apply,
    add_monoid_hom.coe_mk, complex.norm_eq_abs],
  mul_im_I_ax := λ z, by simp only [mul_one, add_monoid_hom.coe_mk, complex.I_im],
  inv_def_ax := λ z, by simp only [complex.inv_def, complex.norm_sq_eq_abs, complex.coe_algebra_map,
    complex.of_real_eq_coe, complex.norm_eq_abs],
  div_I_ax := complex.div_I }

lemma _root_.is_R_or_C.re_eq_complex_re : ⇑(is_R_or_C.re : ℂ →+ ℝ) = complex.re := rfl
lemma _root_.is_R_or_C.im_eq_complex_im : ⇑(is_R_or_C.im : ℂ →+ ℝ) = complex.im := rfl

section

variables {α β γ : Type*}
  [add_comm_monoid α] [topological_space α] [add_comm_monoid γ] [topological_space γ]

/-- The natural `add_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prod_add_hom : ℂ ≃+ ℝ × ℝ :=
{ map_add' := by simp, .. equiv_real_prod }

/-- The natural `linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prod_add_hom_lm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
{ map_smul' := by simp [equiv_real_prod_add_hom], .. equiv_real_prod_add_hom }

/-- The natural `continuous_linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prodₗ : ℂ ≃L[ℝ] ℝ × ℝ :=
equiv_real_prod_add_hom_lm.to_continuous_linear_equiv

end

lemma has_sum_iff {α} (f : α → ℂ) (c : ℂ) :
  has_sum f c ↔ has_sum (λ x, (f x).re) c.re ∧ has_sum (λ x, (f x).im) c.im :=
begin
  -- For some reason, `continuous_linear_map.has_sum` is orders of magnitude faster than
  -- `has_sum.mapL` here:
  refine ⟨λ h, ⟨re_clm.has_sum h, im_clm.has_sum h⟩, _⟩,
  rintro ⟨h₁, h₂⟩,
  convert (h₁.prod_mk h₂).mapL equiv_real_prodₗ.symm.to_continuous_linear_map,
  { ext x; refl },
  { cases c, refl }
end

end complex

namespace is_R_or_C

local notation `reC` := @is_R_or_C.re ℂ _
local notation `imC` := @is_R_or_C.im ℂ _
local notation `IC` := @is_R_or_C.I ℂ _
local notation `absC` := @is_R_or_C.abs ℂ _
local notation `norm_sqC` := @is_R_or_C.norm_sq ℂ _

@[simp] lemma re_to_complex {x : ℂ} : reC x = x.re := rfl
@[simp] lemma im_to_complex {x : ℂ} : imC x = x.im := rfl
@[simp] lemma I_to_complex : IC = complex.I := rfl
@[simp] lemma norm_sq_to_complex {x : ℂ} : norm_sqC x = complex.norm_sq x :=
by simp [is_R_or_C.norm_sq, complex.norm_sq]
@[simp] lemma abs_to_complex {x : ℂ} : absC x = complex.abs x :=
by simp [is_R_or_C.abs, complex.abs]

end is_R_or_C
