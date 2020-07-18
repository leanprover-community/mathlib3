/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import analysis.complex.basic
import analysis.normed_space.operator_norm

/-!
# Extending a continuous ℝ-linear map to a continuous ℂ-linear map

In this file we provide a way to extend a continuous ℝ-linear map to a continuous ℂ-linear map in
a way that bounds the norm by the norm of the original map.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[ℂ] ℂ` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.
-/

open complex

variables {F : Type*} [normed_group F] [normed_space ℂ F]

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[ℂ] ℂ` in a way that will also be continuous and have its norm
bounded by `∥fr∥` if `fr` is continuous. -/
noncomputable def linear_map.extend_to_ℂ (fr : F →ₗ[ℝ] ℝ) : F →ₗ[ℂ] ℂ :=
begin
  let fc : F → ℂ := λ x, ⟨fr x, -fr (I • x)⟩,
  have add : ∀ x y : F, fc (x + y) = fc x + fc y,
  { intros,
    ext; dsimp,
    { rw fr.map_add },
    { rw [smul_add, fr.map_add, neg_add] } },

  have smul_ℝ : ∀ (c : ℝ) (x : F), fc (c • x) = c * fc x,
  { intros,
    ext; dsimp,
    { rw [fr.map_smul, smul_eq_mul, zero_mul, sub_zero] },

    { rw [zero_mul, add_zero],
      calc -fr (I • c • x)
          = -fr (I • (c : ℂ) • x) : rfl
      ... = -fr ((c : ℂ) • I • x) : by rw smul_comm
      ... = -fr (c • I • x) : rfl
      ... = -(c * fr (I • x)) : by rw [fr.map_smul, smul_eq_mul]
      ... = c * -fr (I • x) : by rw neg_mul_eq_mul_neg } },

  have smul_I : ∀ x : F, fc (I • x) = I * fc x,
  { intros,
    have h : -fr (I • I • x) = fr x,
    { calc -fr (I • I • x)
          = -fr (((-1 : ℝ) : ℂ) • x) : by rw [←mul_smul, I_mul_I, of_real_neg, of_real_one]
      ... = -fr ((-1 : ℝ) • x) : rfl
      ... = -((-1 : ℝ) * fr x : ℝ) : by rw [fr.map_smul, smul_eq_mul]
      ... = fr x : by ring },

    { calc fc (I • x)
          = ⟨fr (I • x), -fr (I • I • x)⟩ : rfl
      ... = ⟨fr (I • x), fr x⟩ : by rw h
      ... = I * ⟨fr x, -fr (I • x)⟩ : by rw [I_mul, neg_neg]
      ... = I * fc x : rfl } },

  have smul_ℂ : ∀ (c : ℂ) (x : F), fc (c • x) = c • fc x,
  { intros,
    let a : ℂ := c.re,
    let b : ℂ := c.im,
    have h : fc ((b * I) • x) = b * I * fc x,
    { calc fc ((b * I) • x)
          = fc (b • I • x) : by rw mul_smul
      ... = fc (c.im • I • x) : rfl
      ... = b * fc (I • x) : by rw smul_ℝ
      ... = b * (I * fc x) : by rw smul_I
      ... = b * I * fc x : by rw mul_assoc },

    calc fc (c • x)
        = fc ((a + b * I) • x) : by rw re_add_im
    ... = fc (a • x + (b * I) • x) : by rw add_smul
    ... = fc (a • x) + fc ((b * I) • x) : by rw add
    ... = fc (c.re • x) + fc ((b * I) • x) : rfl
    ... = a * fc x + fc ((b * I) • x) : by rw smul_ℝ
    ... = a * fc x + b * I * fc x : by rw h
    ... = (a + b * I) * fc x : by rw add_mul
    ... = c * fc x : by rw re_add_im c },

  exact { to_fun := fc, map_add' := add, map_smul' := smul_ℂ }
end

/-- The norm of the extension is bounded by ∥fr∥. -/
lemma norm_bound (fr : F →L[ℝ] ℝ) :
  ∀ x : F, ∥fr.to_linear_map.extend_to_ℂ x∥ ≤ ∥fr∥ * ∥x∥ :=
begin
  intros,
  let lm := fr.to_linear_map.extend_to_ℂ,

  -- We aim to find a `t : ℂ` such that
  -- * `lm (t • x) = fr (t • x)` (so `lm (t • x) = t * lm x ∈ ℝ`)
  -- * `∥lm x∥ = ∥lm (t • x)∥` (so `t.abs` must be 1)
  -- If `lm x ≠ 0`, `(lm x)⁻¹` satisfies the first requirement, and after normalizing, it
  -- satisfies the second.
  -- (If `lm x = 0`, the goal is trivial.)
  classical,
  by_cases h : lm x = 0,
  { rw [h, norm_zero],
    apply mul_nonneg; exact norm_nonneg _ },

  let fx := (lm x)⁻¹,
  let t := fx / fx.abs,
  have ht : t.abs = 1,
  { simp only [abs_of_real, of_real_inv, complex.abs_div, complex.abs_inv, complex.abs_abs, t, fx],
    have : abs (lm x) ≠ 0 := abs_ne_zero.mpr h,
    have : (abs (lm x))⁻¹ ≠ 0 := inv_ne_zero this,
    exact div_self this },

  have h1 : (fr (t • x) : ℂ) = lm (t • x),
  { ext,
    { refl },

    { transitivity (0 : ℝ),
      { rw of_real_im },

      { symmetry,
        calc (lm (t • x)).im
            = (t * lm x).im : by rw [lm.map_smul, smul_eq_mul]
        ... = ((lm x)⁻¹ / (lm x)⁻¹.abs * lm x).im : rfl
        ... = (1 / (lm x)⁻¹.abs : ℂ).im : by rw [div_mul_eq_mul_div, inv_mul_cancel h]
        ... = 0 : by rw [←complex.of_real_one, ←of_real_div, of_real_im] } } },

  calc ∥lm x∥
      = t.abs * ∥lm x∥ : by rw [ht, one_mul]
  ... = ∥t * lm x∥ : by rw [normed_field.norm_mul, t.norm_eq_abs]
  ... = ∥lm (t • x)∥ : by rw [←smul_eq_mul, lm.map_smul]
  ... = ∥(fr (t • x) : ℂ)∥ : by rw h1
  ... = ∥fr (t • x)∥ : by rw norm_real
  ... ≤ ∥fr∥ * ∥t • x∥ : continuous_linear_map.le_op_norm _ _
  ... = ∥fr∥ * (∥t∥ * ∥x∥) : by rw norm_smul
  ... = ∥fr∥ * ∥x∥ : by rw [norm_eq_abs, ht, one_mul],
end

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[ℂ] ℂ`. -/
noncomputable def continuous_linear_map.extend_to_ℂ (fr : F →L[ℝ] ℝ) : F →L[ℂ] ℂ :=
  fr.to_linear_map.extend_to_ℂ.mk_continuous ∥fr∥ (norm_bound _)
