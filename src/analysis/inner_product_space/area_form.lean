/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation


noncomputable theory

open_locale real_inner_product_space
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables {E : Type*} [inner_product_space ℝ E] [fact (finrank ℝ E = 2)]
  (o : orientation ℝ E (fin 2))

include o

namespace orientation

def area_form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
begin
  let to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
    (inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm,
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  exact y ∘ₗ (alternating_map.curry_left_linear_map o.volume_form),
end

local notation `ω` := o.area_form

lemma area_form_to_volume_form (x y : E) : ω x y = o.volume_form ![x, y] := by simp [area_form]

attribute [irreducible] area_form

@[simp] lemma area_form_apply_self (x : E) : ω x x = 0 :=
begin
  rw area_form_to_volume_form,
  refine o.volume_form.map_eq_zero_of_eq ![x, x] _ (_ : (0 : fin 2) ≠ 1),
  { simp },
  { norm_num }
end

lemma area_form_swap (x y : E) : ω x y = - ω y x :=
begin
  simp only [area_form_to_volume_form],
  convert o.volume_form.map_swap ![y, x] (_ : (0 : fin 2) ≠ 1),
  { ext i,
    fin_cases i; refl },
  { norm_num }
end

def almost_complex : E →ₗ[ℝ] E :=
begin
  let to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
    (inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm,
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  let y' : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ (alternating_map ℝ E ℝ (fin 1)) (E →ₗ[ℝ] ℝ) E to_dual.symm) y,
  exact y' ∘ₗ (alternating_map.curry_left_linear_map o.volume_form),
end

local notation `J` := o.almost_complex

lemma almost_complex_to_volume_form (x y : E) : ⟪J x, y⟫ = o.volume_form ![x, y] :=
by simp only [almost_complex, linear_equiv.trans_symm, linear_equiv.symm_symm,
  linear_isometry_equiv.to_linear_equiv_symm, alternating_map.curry_left_linear_map_apply,
  linear_map.coe_comp, function.comp_app, linear_map.llcomp_apply,
  linear_equiv.coe_coe, linear_equiv.trans_apply, linear_isometry_equiv.coe_to_linear_equiv,
  linear_isometry_equiv.norm_map, submodule.coe_norm,
  inner_product_space.to_dual_symm_apply, alternating_map.curry_left_apply_apply,
  alternating_map.const_linear_equiv_of_is_empty_symm_apply,
  eq_self_iff_true, linear_map.coe_to_continuous_linear_map', matrix.zero_empty]

attribute [irreducible] area_form

@[simp] lemma inner_almost_complex_apply (x y : E) : ⟪J x, y⟫ = ω x y :=
by rw [area_form_to_volume_form, almost_complex_to_volume_form]


section orthonormal_basis

lemma area_form_apply_orthonormal_basis (b : orthonormal_basis (fin 2) ℝ E)
  (h : b.to_basis.orientation = o) (x y : E) :
  ω x y = ⟪x, b 0⟫ * ⟪y, b 1⟫ - ⟪x, b 1⟫ * ⟪y, b 0⟫ :=
sorry

end orthonormal_basis

end orientation
