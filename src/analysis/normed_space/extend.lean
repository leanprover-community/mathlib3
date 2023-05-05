/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import analysis.normed_space.operator_norm
import algebra.algebra.restrict_scalars
import data.is_R_or_C.basic

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `linear_map.extend_to_𝕜`
* `continuous_linear_map.extend_to_𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars ℝ 𝕜 F`.
Alternate forms which operate on `[is_scalar_tower ℝ 𝕜 F]` instead are provided with a primed name.

-/

open is_R_or_C
open_locale complex_conjugate

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [seminormed_add_comm_group F] [normed_space 𝕜 F]

namespace linear_map

variables [module ℝ F] [is_scalar_tower ℝ 𝕜 F]

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `‖fr‖` if `fr` is continuous. -/
noncomputable def extend_to_𝕜' (fr : F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
begin
  let fc : F → 𝕜 := λ x, (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x)),
  have add : ∀ x y : F, fc (x + y) = fc x + fc y,
  { assume x y,
    simp only [fc],
    simp only [smul_add, linear_map.map_add, of_real_add],
    rw mul_add,
    abel, },
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜),
  { assume c x,
    rw [← of_real_mul],
    congr' 1,
    rw [is_R_or_C.of_real_alg, smul_assoc, fr.map_smul, algebra.id.smul_eq_mul, one_smul] },
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x,
  { assume c x,
    simp only [fc, A],
    rw A c x,
    rw [smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub],
    ring },
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x,
  { assume x,
    simp only [fc],
    cases @I_mul_I_ax 𝕜 _ with h h, { simp [h] },
    rw [mul_sub, ← mul_assoc, smul_smul, h],
    simp only [neg_mul, linear_map.map_neg, one_mul, one_smul,
      mul_neg, of_real_neg, neg_smul, sub_neg_eq_add, add_comm] },
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x,
  { assume c x,
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc],
    refl },
  exact { to_fun := fc, map_add' := add, map_smul' := smul_𝕜 }
end

lemma extend_to_𝕜'_apply (fr : F →ₗ[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜' x = (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x) := rfl

@[simp] lemma extend_to_𝕜'_apply_re (fr : F →ₗ[ℝ] ℝ) (x : F) : re (fr.extend_to_𝕜' x : 𝕜) = fr x :=
by simp only [extend_to_𝕜'_apply, map_sub, zero_mul, mul_zero, sub_zero] with is_R_or_C_simps

lemma norm_extend_to_𝕜'_apply_sq (f : F →ₗ[ℝ] ℝ) (x : F) :
  ‖(f.extend_to_𝕜' x : 𝕜)‖ ^ 2 = f (conj (f.extend_to_𝕜' x : 𝕜) • x) :=
calc ‖(f.extend_to_𝕜' x : 𝕜)‖ ^ 2 = re (conj (f.extend_to_𝕜' x) * f.extend_to_𝕜' x : 𝕜) :
  by rw [is_R_or_C.conj_mul, norm_sq_eq_def', of_real_re]
... = f (conj (f.extend_to_𝕜' x : 𝕜) • x) :
  by rw [← smul_eq_mul, ← map_smul, extend_to_𝕜'_apply_re]

end linear_map

namespace continuous_linear_map

variables [normed_space ℝ F] [is_scalar_tower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
lemma norm_extend_to_𝕜'_bound (fr : F →L[ℝ] ℝ) (x : F) :
  ‖(fr.to_linear_map.extend_to_𝕜' x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ :=
begin
  set lm : F →ₗ[𝕜] 𝕜 := fr.to_linear_map.extend_to_𝕜',
  classical,
  by_cases h : lm x = 0,
  { rw [h, norm_zero],
    apply mul_nonneg; exact norm_nonneg _ },
  rw [← mul_le_mul_left (norm_pos_iff.2 h), ← sq],
  calc ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) : fr.to_linear_map.norm_extend_to_𝕜'_apply_sq x
  ... ≤ ‖fr (conj (lm x : 𝕜) • x)‖ : le_abs_self _
  ... ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ : le_op_norm _ _
  ... = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) : by rw [norm_smul, norm_conj, mul_left_comm]
end

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def extend_to_𝕜' (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
linear_map.mk_continuous _ (‖fr‖) fr.norm_extend_to_𝕜'_bound

lemma extend_to_𝕜'_apply (fr : F →L[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜' x = (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x) := rfl

@[simp] lemma norm_extend_to_𝕜' (fr : F →L[ℝ] ℝ) : ‖(fr.extend_to_𝕜' : F →L[𝕜] 𝕜)‖ = ‖fr‖ :=
le_antisymm (linear_map.mk_continuous_norm_le _ (norm_nonneg _) _) $
  op_norm_le_bound _ (norm_nonneg _) $ λ x,
    calc ‖fr x‖ = ‖re (fr.extend_to_𝕜' x : 𝕜)‖ : congr_arg norm (fr.extend_to_𝕜'_apply_re x).symm
    ... ≤ ‖(fr.extend_to_𝕜' x : 𝕜)‖ : (abs_re_le_abs _).trans_eq (norm_eq_abs _).symm
    ... ≤ ‖(fr.extend_to_𝕜' : F →L[𝕜] 𝕜)‖ * ‖x‖ : le_op_norm _ _

end continuous_linear_map

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜`. -/
noncomputable def linear_map.extend_to_𝕜 (fr : (restrict_scalars ℝ 𝕜 F) →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
fr.extend_to_𝕜'

lemma linear_map.extend_to_𝕜_apply (fr : (restrict_scalars ℝ 𝕜 F) →ₗ[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜 x = (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x : _) := rfl

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def continuous_linear_map.extend_to_𝕜 (fr : (restrict_scalars ℝ 𝕜 F) →L[ℝ] ℝ) :
  F →L[𝕜] 𝕜 :=
fr.extend_to_𝕜'

lemma continuous_linear_map.extend_to_𝕜_apply (fr : (restrict_scalars ℝ 𝕜 F) →L[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜 x = (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x : _) := rfl

@[simp] lemma continuous_linear_map.norm_extend_to_𝕜 (fr : (restrict_scalars ℝ 𝕜 F) →L[ℝ] ℝ) :
  ‖fr.extend_to_𝕜‖ = ‖fr‖ :=
fr.norm_extend_to_𝕜'
