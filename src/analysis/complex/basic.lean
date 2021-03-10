/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.complex.module
import data.complex.is_R_or_C

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `continuous_linear_map.re`
* `continuous_linear_map.im`
* `continuous_linear_map.of_real`

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as continuous `ℝ`-linear maps.

We also register the fact that `ℂ` is an `is_R_or_C` field.
-/
noncomputable theory


namespace complex

instance : has_norm ℂ := ⟨abs⟩

instance : normed_group ℂ :=
normed_group.of_core ℂ
{ norm_eq_zero_iff := λ z, abs_eq_zero,
  triangle := abs_add,
  norm_neg := abs_neg }

instance : normed_field ℂ :=
{ norm := abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := abs_mul,
  .. complex.field }

instance : nondiscrete_normed_field ℂ :=
{ non_trivial := ⟨2, by simp [norm]; norm_num⟩ }

instance normed_algebra_over_reals : normed_algebra ℝ ℂ :=
{ norm_algebra_map_eq := abs_of_real,
  ..complex.algebra_over_reals }

@[simp] lemma norm_eq_abs (z : ℂ) : ∥z∥ = abs z := rfl

lemma dist_eq (z w : ℂ) : dist z w = abs (z - w) := rfl

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = _root_.abs (r : ℝ) :=
suffices ∥((r : ℝ) : ℂ)∥ = _root_.abs r, by simpa,
by rw [norm_real, real.norm_eq_abs]

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ∥(n : ℂ)∥ = _root_.abs n :=
suffices ∥((n : ℝ) : ℂ)∥ = _root_.abs n, by simpa,
by rw [norm_real, real.norm_eq_abs]

lemma norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n :=
by rw [norm_int, _root_.abs_of_nonneg]; exact int.cast_nonneg.2 hn

/-- A complex normed vector space is also a real normed vector space. -/
@[priority 900]
instance normed_space.restrict_scalars_real (E : Type*) [normed_group E] [normed_space ℂ E] :
  normed_space ℝ E := normed_space.restrict_scalars ℝ ℂ E

open continuous_linear_map

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_clm : ℂ →L[ℝ] ℝ :=
linear_map.re.mk_continuous 1 (λ x, by simp [real.norm_eq_abs, abs_re_le_abs])

@[continuity] lemma continuous_re : continuous re := re_clm.continuous

@[simp] lemma re_clm_coe : (coe (re_clm) : ℂ →ₗ[ℝ] ℝ) = linear_map.re := rfl

@[simp] lemma re_clm_apply (z : ℂ) : (re_clm : ℂ → ℝ) z = z.re := rfl

@[simp] lemma re_clm_norm : ∥re_clm∥ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ∥re_clm 1∥ : by simp
   ... ≤ ∥re_clm∥ : unit_le_op_norm _ _ (by simp)

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def im_clm : ℂ →L[ℝ] ℝ :=
linear_map.im.mk_continuous 1 (λ x, by simp [real.norm_eq_abs, abs_im_le_abs])

@[continuity] lemma continuous_im : continuous im := im_clm.continuous

@[simp] lemma im_clm_coe : (coe (im_clm) : ℂ →ₗ[ℝ] ℝ) = linear_map.im := rfl

@[simp] lemma im_clm_apply (z : ℂ) : (im_clm : ℂ → ℝ) z = z.im := rfl

@[simp] lemma im_clm_norm : ∥im_clm∥ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ∥im_clm I∥ : by simp
   ... ≤ ∥im_clm∥ : unit_le_op_norm _ _ (by simp)

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear map. -/
def conj_li : ℂ →ₗᵢ[ℝ] ℂ := ⟨linear_map.conj, λ x, by simp⟩

/-- Continuous linear map version of the conj function, from `ℂ` to `ℂ`. -/
def conj_clm : ℂ →L[ℝ] ℂ := conj_li.to_continuous_linear_map

lemma isometry_conj : isometry (conj : ℂ → ℂ) := conj_li.isometry

@[continuity] lemma continuous_conj : continuous conj := conj_clm.continuous

@[simp] lemma conj_clm_coe : (coe (conj_clm) : ℂ →ₗ[ℝ] ℂ) = linear_map.conj := rfl

@[simp] lemma conj_clm_apply (z : ℂ) : (conj_clm : ℂ → ℂ) z = z.conj := rfl

@[simp] lemma conj_clm_norm : ∥conj_clm∥ = 1 := conj_li.norm_to_continuous_linear_map

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_li : ℝ →ₗᵢ[ℝ] ℂ := ⟨linear_map.of_real, λ x, by simp⟩

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_clm : ℝ →L[ℝ] ℂ := of_real_li.to_continuous_linear_map

lemma isometry_of_real : isometry (coe : ℝ → ℂ) := of_real_li.isometry

@[continuity] lemma continuous_of_real : continuous (coe : ℝ → ℂ) := isometry_of_real.continuous

@[simp] lemma of_real_clm_coe : (coe (of_real_clm) : ℝ →ₗ[ℝ] ℂ) = linear_map.of_real := rfl

@[simp] lemma of_real_clm_apply (x : ℝ) : (of_real_clm : ℝ → ℂ) x = x := rfl

@[simp] lemma of_real_clm_norm : ∥of_real_clm∥ = 1 := of_real_li.norm_to_continuous_linear_map

noncomputable instance : is_R_or_C ℂ :=
{ re := ⟨complex.re, complex.zero_re, complex.add_re⟩,
  im := ⟨complex.im, complex.zero_im, complex.add_im⟩,
  conj := complex.conj,
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
  conj_re_ax := λ z, by simp only [ring_hom.coe_mk, add_monoid_hom.coe_mk, complex.conj_re],
  conj_im_ax := λ z, by simp only [ring_hom.coe_mk, complex.conj_im, add_monoid_hom.coe_mk],
  conj_I_ax := by simp only [complex.conj_I, ring_hom.coe_mk],
  norm_sq_eq_def_ax := λ z, by simp only [←complex.norm_sq_eq_abs, ←complex.norm_sq_apply,
    add_monoid_hom.coe_mk, complex.norm_eq_abs],
  mul_im_I_ax := λ z, by simp only [mul_one, add_monoid_hom.coe_mk, complex.I_im],
  inv_def_ax := λ z, by simp only [complex.inv_def, complex.norm_sq_eq_abs, complex.coe_algebra_map,
    complex.of_real_eq_coe, complex.norm_eq_abs],
  div_I_ax := complex.div_I }

end complex

namespace is_R_or_C

local notation `reC` := @is_R_or_C.re ℂ _
local notation `imC` := @is_R_or_C.im ℂ _
local notation `conjC` := @is_R_or_C.conj ℂ _
local notation `IC` := @is_R_or_C.I ℂ _
local notation `absC` := @is_R_or_C.abs ℂ _
local notation `norm_sqC` := @is_R_or_C.norm_sq ℂ _

@[simp] lemma re_to_complex {x : ℂ} : reC x = x.re := rfl
@[simp] lemma im_to_complex {x : ℂ} : imC x = x.im := rfl
@[simp] lemma conj_to_complex {x : ℂ} : conjC x = x.conj := rfl
@[simp] lemma I_to_complex : IC = complex.I := rfl
@[simp] lemma norm_sq_to_complex {x : ℂ} : norm_sqC x = complex.norm_sq x :=
by simp [is_R_or_C.norm_sq, complex.norm_sq]
@[simp] lemma abs_to_complex {x : ℂ} : absC x = complex.abs x :=
by simp [is_R_or_C.abs, complex.abs]

end is_R_or_C
