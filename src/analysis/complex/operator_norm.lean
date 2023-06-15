/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.complex.basic
import analysis.normed_space.operator_norm
import data.complex.determinant

/-! # The basic continuous linear maps associated to `ℂ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The continuous linear maps `complex.re_clm` (real part), `complex.im_clm` (imaginary part),
`complex.conj_cle` (conjugation), and `complex.of_real_clm` (inclusion of `ℝ`) were introduced in
`analysis.complex.operator_norm`.  This file contains a few calculations requiring more imports:
the operator norm and (for `complex.conj_cle`) the determinant.
-/

open continuous_linear_map

namespace complex

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp] lemma det_conj_lie : (conj_lie.to_linear_equiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
det_conj_ae

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp] lemma linear_equiv_det_conj_lie : conj_lie.to_linear_equiv.det = -1 :=
linear_equiv_det_conj_ae

@[simp] lemma re_clm_norm : ‖re_clm‖ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ‖re_clm 1‖ : by simp
   ... ≤ ‖re_clm‖ : unit_le_op_norm _ _ (by simp)

@[simp] lemma re_clm_nnnorm : ‖re_clm‖₊ = 1 := subtype.ext re_clm_norm

@[simp] lemma im_clm_norm : ‖im_clm‖ = 1 :=
le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _) $
calc 1 = ‖im_clm I‖ : by simp
   ... ≤ ‖im_clm‖ : unit_le_op_norm _ _ (by simp)

@[simp] lemma im_clm_nnnorm : ‖im_clm‖₊ = 1 := subtype.ext im_clm_norm

@[simp] lemma conj_cle_norm : ‖(conj_cle : ℂ →L[ℝ] ℂ)‖ = 1 :=
conj_lie.to_linear_isometry.norm_to_continuous_linear_map

@[simp] lemma conj_cle_nnorm : ‖(conj_cle : ℂ →L[ℝ] ℂ)‖₊ = 1 := subtype.ext conj_cle_norm

@[simp] lemma of_real_clm_norm : ‖of_real_clm‖ = 1 := of_real_li.norm_to_continuous_linear_map

@[simp] lemma of_real_clm_nnnorm : ‖of_real_clm‖₊ = 1 := subtype.ext $ of_real_clm_norm

end complex
