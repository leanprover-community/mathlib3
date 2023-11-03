/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.calculus.conformal.normed_space
import analysis.inner_product_space.calculus
import analysis.inner_product_space.conformal_linear_map

/-!
# Conformal maps between inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function between inner product spaces is which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/

noncomputable theory

variables {E F : Type*}
variables [normed_add_comm_group E] [normed_add_comm_group F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]

open_locale real_inner_product_space

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff' {f : E → F} {x : E} :
  conformal_at f x ↔
  ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
by rw [conformal_at_iff_is_conformal_map_fderiv, is_conformal_map_iff]

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `f'` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : has_fderiv_at f f' x) :
  conformal_at f x ↔ ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪f' u, f' v⟫ = c * ⟪u, v⟫ :=
by simp only [conformal_at_iff', h.fderiv]

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformal_factor_at {f : E → F} {x : E} (h : conformal_at f x) : ℝ :=
classical.some (conformal_at_iff'.mp h)

lemma conformal_factor_at_pos {f : E → F} {x : E} (h : conformal_at f x) :
  0 < conformal_factor_at h :=
(classical.some_spec $ conformal_at_iff'.mp h).1

lemma conformal_factor_at_inner_eq_mul_inner' {f : E → F} {x : E}
  (h : conformal_at f x) (u v : E) :
  ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformal_factor_at h : ℝ) * ⟪u, v⟫ :=
(classical.some_spec $ conformal_at_iff'.mp h).2 u v

lemma conformal_factor_at_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) (u v : E) :
  ⟪f' u, f' v⟫ = (conformal_factor_at H : ℝ) * ⟪u, v⟫ :=
(H.differentiable_at.has_fderiv_at.unique h) ▸ conformal_factor_at_inner_eq_mul_inner' H u v


section conformal_inversion

open continuous_linear_map

lemma fderiv_inversion {X : Type*} [inner_product_space ℝ X]
  {r : ℝ} (hr : 0 < r) {x₀ : X} {y x : X} (hx : x ≠ x₀) :
  fderiv ℝ (inversion hr x₀) x y = r • (∥x - x₀∥ ^ 4)⁻¹ •
  (∥x - x₀∥ ^ 2 • y - (2 : ℝ) • ⟪y, x - x₀⟫ • (x - x₀)) :=
begin
  have triv₁ : ⟪x - x₀, x - x₀⟫ ≠ 0 := λ w, (sub_ne_zero.mpr hx) (inner_self_eq_zero.mp w),
  have triv₂ : ∥x - x₀∥ ≠ 0 := λ w, hx (norm_sub_eq_zero_iff.mp w),
  simp only [inversion],
  rw [fderiv_const_add, fderiv_smul _ (differentiable_at_id'.sub_const _),
      fderiv_sub_const, fderiv_id', fderiv_const_mul],
  simp only [pow_two, ← real_inner_self_eq_norm_sq],
  have minor₁ := differentiable_at_inv.mpr triv₁,
  rw [fderiv.comp, fderiv_inv],
  simp only [add_apply, smul_right_apply, smul_apply, coe_comp', function.comp_app, one_apply,
             id_apply],
  rw fderiv_inner_apply (differentiable_at_id'.sub_const x₀) (differentiable_at_id'.sub_const x₀),
  rw [fderiv_sub_const, fderiv_id'],
  simp only [id_apply, congr_arg],
  { rw [real_inner_self_eq_norm_sq, ← pow_two] at triv₁,
    nth_rewrite 2 real_inner_comm,
    simp only [smul_smul, real_inner_self_eq_norm_sq, ← pow_two, smul_sub, smul_smul],
    simp only [smul_eq_mul, mul_add, add_mul, add_smul],
    nth_rewrite 10 mul_comm,
    have : ∥x - x₀∥ ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ = (∥x - x₀∥ ^ 2)⁻¹ :=
      by field_simp [triv₁]; rw ← pow_add; norm_num; rw div_self (pow_ne_zero _ triv₂),
    rw this,
    simp only [← pow_mul],
    norm_num,
    simp only [← neg_add, sub_neg_eq_add, ← sub_add, two_mul, mul_add, add_smul],
    rw [real_inner_comm, real_inner_comm, real_inner_comm, real_inner_comm],
    ring_nf,
    simp only [← add_assoc, ← sub_eq_add_neg] },
  { exact differentiable_at_inv.mpr triv₁ },
  { exact (differentiable_at_id'.sub_const x₀).inner (differentiable_at_id'.sub_const x₀) },
  { refine (differentiable_at_inv.mpr _).comp _ (differentiable_at_id'.sub_const x₀).norm_sq,
    convert triv₁,
    rw [real_inner_self_eq_norm_sq, pow_two] },
  { apply_instance },
  { refine ((differentiable_at_inv.mpr _).comp _
      (differentiable_at_id'.sub_const x₀).norm_sq).const_mul _,
    convert triv₁,
    rw [real_inner_self_eq_norm_sq, pow_two] }
end

lemma is_conformal_map_fderiv_inversion_aux {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) (v : E) :
  ⟪fderiv ℝ (inversion hr x₀) x v, fderiv ℝ (inversion hr x₀) x v⟫ =
  r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ * ⟪v, v⟫ :=
begin
  let x' := x - x₀,
  have this : ∥x'∥ ^ 4 ≠ 0 :=
    pow_ne_zero 4 (ne_of_gt $ norm_pos_iff.mpr $ λ w, (sub_ne_zero.mpr hx) w),
  simp only [← x', fderiv_inversion hr hx, real_inner_smul_left, real_inner_smul_right],
  rw [inner_sub_left, inner_sub_right],
  nth_rewrite 1 inner_sub_right,
  simp only [real_inner_smul_left, real_inner_smul_right],
  rw [real_inner_self_eq_norm_sq x', ← pow_two],
  nth_rewrite 4 real_inner_comm,
  ring_nf,
  simp only [pow_two],
  field_simp [this],
  ring
end

lemma is_conformal_map_fderiv_inversion_aux' {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) (u v : E) :
  ⟪fderiv ℝ (inversion hr x₀) x u, fderiv ℝ (inversion hr x₀) x v⟫ =
  r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ * ⟪u, v⟫ :=
begin
  have minor₁ := is_conformal_map_fderiv_inversion_aux hr hx u,
  have minor₂ := is_conformal_map_fderiv_inversion_aux hr hx v,
  have minor₃ := is_conformal_map_fderiv_inversion_aux hr hx (u + v),
  simp only [continuous_linear_map.map_add, inner_add_left, inner_add_right] at minor₃,
  rw [minor₁, minor₂] at minor₃,
  nth_rewrite 1 real_inner_comm at minor₃,
  nth_rewrite 5 real_inner_comm at minor₃,
  simp only [mul_add, add_assoc] at minor₃,
  have minor₄ := add_left_cancel minor₃,
  simp only [← add_assoc] at minor₄,
  simpa [← mul_two] using add_right_cancel minor₄
end

lemma is_conformal_map_fderiv_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  is_conformal_map (fderiv ℝ (inversion hr x₀) x) :=
begin
  have triv₁ : 0 < (∥x - x₀∥ ^ 4)⁻¹ := inv_pos.mpr
    (pow_pos (norm_pos_iff.mpr $ λ w, (sub_ne_zero.mpr hx) w) _),
  exact (is_conformal_map_iff _).mpr ⟨r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹, mul_pos (pow_pos hr _) triv₁,
    is_conformal_map_fderiv_inversion_aux' hr hx⟩
end

lemma conformal_at_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  conformal_at (inversion hr x₀) x :=
conformal_at_iff_is_conformal_map_fderiv.mpr (is_conformal_map_fderiv_inversion hr hx)

end conformal_inversion
