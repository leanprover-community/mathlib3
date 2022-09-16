/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation
import tactic.linear_combination


noncomputable theory

open_locale real_inner_product_space complex_conjugate
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

section foo
variables {R R₂ E E₂ : Type*} [semiring R] [semiring R₂]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  [seminormed_add_comm_group E] [seminormed_add_comm_group E₂] [module R E] [module R₂ E₂]

def linear_isometry_equiv.of_linear_isometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
  (h₁ : f.to_linear_map.comp g = linear_map.id) (h₂ : g.comp f.to_linear_map = linear_map.id) :
  E ≃ₛₗᵢ[σ₁₂] E₂ :=
{ norm_map' := λ x, f.norm_map x,
  .. linear_equiv.of_linear f.to_linear_map g h₁ h₂ }

@[simp] lemma linear_isometry_equiv.coe_of_linear_isometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
  (h₁ : f.to_linear_map.comp g = linear_map.id) (h₂ : g.comp f.to_linear_map = linear_map.id) :
  (linear_isometry_equiv.of_linear_isometry f g h₁ h₂ : E → E₂) = (f : E → E₂) :=
rfl

@[simp] lemma linear_isometry_equiv.coe_of_linear_isometry_symm (f : E →ₛₗᵢ[σ₁₂] E₂)
  (g : E₂ →ₛₗ[σ₂₁] E) (h₁ : f.to_linear_map.comp g = linear_map.id)
  (h₂ : g.comp f.to_linear_map = linear_map.id) :
  ((linear_isometry_equiv.of_linear_isometry f g h₁ h₂).symm : E₂ → E) = (g : E₂ → E) :=
rfl

end foo

variables {E : Type*} [inner_product_space ℝ E] [fact (finrank ℝ E = 2)]
  (o : orientation ℝ E (fin 2))

include o

namespace orientation

def area_form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
begin
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

lemma abs_area_form_le (x y : E) : |ω x y| ≤ ∥x∥ * ∥y∥ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.abs_volume_form_apply_le ![x, y]

lemma area_form_le (x y : E) : ω x y ≤ ∥x∥ * ∥y∥ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.volume_form_apply_le ![x, y]

lemma abs_area_form_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ∥x∥ * ∥y∥ :=
begin
  rw [o.area_form_to_volume_form, o.abs_volume_form_apply_of_pairwise_orthogonal],
  { simp [fin.prod_univ_succ] },
  intros i j hij,
  fin_cases i; fin_cases j,
  { simpa },
  { simpa using h },
  { simpa [real_inner_comm] using h },
  { simpa }
end

def almost_complex_aux₁ : E →ₗ[ℝ] E :=
let to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
  (inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm in
↑to_dual.symm ∘ₗ ω

@[simp] lemma inner_almost_complex_aux₁_left (x y : E) : ⟪o.almost_complex_aux₁ x, y⟫ = ω x y :=
by simp [almost_complex_aux₁]

attribute [irreducible] almost_complex_aux₁

@[simp] lemma inner_almost_complex_aux₁_right (x y : E) : ⟪x, o.almost_complex_aux₁ y⟫ = - ω x y :=
begin
  rw real_inner_comm,
  simp [o.area_form_swap y x],
end

def almost_complex_aux₂ : E →ₗᵢ[ℝ] E :=
{ norm_map' := λ x, begin
    dsimp,
    refine le_antisymm _ _,
    { cases eq_or_lt_of_le (norm_nonneg (o.almost_complex_aux₁ x)) with h h,
      { rw ← h,
        positivity },
      refine le_of_mul_le_mul_right' _ h,
      rw [← real_inner_self_eq_norm_mul_norm, o.inner_almost_complex_aux₁_left],
      exact o.area_form_le x (o.almost_complex_aux₁ x) },
    { let K : submodule ℝ E := ℝ ∙ x,
      haveI : nontrivial Kᗮ,
      { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
        have : finrank ℝ K ≤ finset.card {x},
        { rw ← set.to_finset_singleton,
          exact finrank_span_le_card ({x} : set E) },
        have : finset.card {x} = 1 := finset.card_singleton x,
        have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal,
        have : finrank ℝ E = 2 := fact.out _,
        linarith },
      obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0,
      have hw' : ⟪x, (w:E)⟫ = 0 := inner_right_of_mem_orthogonal_singleton x w.2, -- hw'₀,
      have hw : (w:E) ≠ 0 := λ h, hw₀ (submodule.coe_eq_zero.mp h),
      refine le_of_mul_le_mul_right' _ (by rwa norm_pos_iff : 0 < ∥(w:E)∥),
      rw ← o.abs_area_form_of_orthogonal hw',
      rw ← o.inner_almost_complex_aux₁_left x w,
      exact abs_real_inner_le_norm (o.almost_complex_aux₁ x) w },
  end,
  .. o.almost_complex_aux₁ }

@[simp] lemma almost_complex_aux₁_almost_complex_aux₁ (x : E) :
  o.almost_complex_aux₁ (o.almost_complex_aux₁ x) = - x :=
begin
  apply ext_inner_left ℝ,
  intros y,
  have : ⟪o.almost_complex_aux₁ y, o.almost_complex_aux₁ x⟫ = ⟪y, x⟫ :=
    linear_isometry.inner_map_map o.almost_complex_aux₂ y x,
  rw [o.inner_almost_complex_aux₁_right, ← o.inner_almost_complex_aux₁_left, this, inner_neg_right],
end

def almost_complex : E ≃ₗᵢ[ℝ] E :=
linear_isometry_equiv.of_linear_isometry
  o.almost_complex_aux₂
  (-o.almost_complex_aux₁)
  (by ext; simp [almost_complex_aux₂])
  (by ext; simp [almost_complex_aux₂])

local notation `J` := o.almost_complex

@[simp] lemma inner_almost_complex_left (x y : E) : ⟪J x, y⟫ = ω x y :=
o.inner_almost_complex_aux₁_left x y

@[simp] lemma inner_almost_complex_right (x y : E) : ⟪x, J y⟫ = - ω x y :=
o.inner_almost_complex_aux₁_right x y

@[simp] lemma almost_complex_almost_complex (x : E) : J (J x) = - x :=
o.almost_complex_aux₁_almost_complex_aux₁ x

@[simp] lemma almost_complex_symm :
  linear_isometry_equiv.symm J = linear_isometry_equiv.trans J (linear_isometry_equiv.neg ℝ) :=
linear_isometry_equiv.to_linear_isometry_injective rfl

attribute [irreducible] almost_complex

@[simp] lemma inner_almost_complex_self (x : E) : ⟪J x, x⟫ = 0 := by simp

lemma inner_almost_complex_swap (x y : E) : ⟪x, J y⟫ = - ⟪J x, y⟫ := by simp

lemma inner_almost_complex_swap' (x y : E) : ⟪J x, y⟫ = - ⟪x, J y⟫ :=
by simp [o.inner_almost_complex_swap x y]

lemma inner_comp_almost_complex (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
linear_isometry_equiv.inner_map_map J x y

@[simp] lemma almost_complex_trans_almost_complex :
  linear_isometry_equiv.trans J J = linear_isometry_equiv.neg ℝ :=
by ext; simp

def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
(linear_map.llcomp ℝ E ℝ ℂ complex.of_real_clm) ∘ₗ (@innerₛₗ ℝ E _ _)
+ (linear_map.llcomp ℝ E ℝ ℂ ((linear_map.lsmul ℝ ℂ).flip complex.I)) ∘ₗ ω

lemma kahler_apply (x : E) :
  o.kahler x
  = ↑complex.of_real_clm ∘ₗ @innerₛₗ ℝ E _ _ x + linear_map.smul_right (ω x) complex.I :=
rfl

@[simp] lemma kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • complex.I := rfl

lemma kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) :=
begin
  simp only [kahler_apply_apply],
  rw [real_inner_comm, area_form_swap],
  simp,
end

lemma norm_sq_kahler (x y : E) : complex.norm_sq (o.kahler x y) = ∥x∥ ^ 2 * ∥y∥ ^ 2 :=
begin
  simp [complex.norm_sq],
  sorry
end

lemma abs_kahler (x y : E) : complex.abs (o.kahler x y) = ∥x∥ * ∥y∥ :=
begin
  rw [← sq_eq_sq, complex.sq_abs],
  { linear_combination o.norm_sq_kahler x y },
  { exact complex.abs_nonneg _ },
  { positivity }
end

lemma norm_kahler (x y : E) : ∥o.kahler x y∥ = ∥x∥ * ∥y∥ := by simpa using o.abs_kahler x y

lemma eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 :=
begin
  have : ∥x∥ * ∥y∥ = 0 := by simpa [hx] using (o.norm_kahler x y).symm,
  cases eq_zero_or_eq_zero_of_mul_eq_zero this with h h,
  { left,
    simpa using h },
  { right,
    simpa using h },
end

lemma kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, _⟩,
  rintros (rfl | rfl);
  simp,
end

lemma kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 :=
begin
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero,
  tauto,
end

lemma kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 :=
begin
  refine ⟨_, λ h, o.kahler_ne_zero h.1 h.2⟩,
  contrapose,
  simp only [not_and_distrib, not_not, kahler_apply_apply, complex.real_smul],
  rintros (rfl | rfl);
  simp,
end

section orthonormal_basis

lemma area_form_apply_orthonormal_basis (b : orthonormal_basis (fin 2) ℝ E)
  (h : b.to_basis.orientation = o) (x y : E) :
  ω x y = ⟪x, b 0⟫ * ⟪y, b 1⟫ - ⟪x, b 1⟫ * ⟪y, b 0⟫ :=
sorry

end orthonormal_basis

end orientation
