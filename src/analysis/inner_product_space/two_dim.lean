/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation
import tactic.linear_combination

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `orientation.area_form`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `orientation.right_angle_rotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1.  In a later file, rotations (`orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `orientation.basis_right_angle_rotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `orientation.area_form`.  For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `orientation.right_angle_rotation_right_angle_rotation`: the identity `J (J x) = - x`

* `orientation.nonneg_inner_and_area_form_eq_zero_iff_same_ray`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `complex.area_form`, `complex.right_angle_rotation`, `complex.kahler`: the concrete
  interpretations of `area_form`, `right_angle_rotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `orientation.area_form_map_complex`, `orientation.right_angle_rotation_map_complex`,
  `orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `area_form`, `right_angle_rotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `orientation.area_form` and `J` for `orientation.right_angle_rotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`).  Write

```
local notation `ω` := o.area_form
local notation `J` := o.right_angle_rotation
```

-/

noncomputable theory

open_locale real_inner_product_space complex_conjugate
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables {E : Type*} [inner_product_space ℝ E] [fact (finrank ℝ E = 2)]
  (o : orientation ℝ E (fin 2))

namespace orientation

include o

/-- An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual
notation `ω`).  When evaluated on two vectors, it gives the oriented area of the parallelogram they
span. -/
@[irreducible] def area_form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
begin
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  exact y ∘ₗ (alternating_map.curry_left_linear_map o.volume_form),
end

omit o

local notation `ω` := o.area_form

lemma area_form_to_volume_form (x y : E) : ω x y = o.volume_form ![x, y] := by simp [area_form]

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

@[simp] lemma area_form_neg_orientation : (-o).area_form = -o.area_form :=
begin
  ext x y,
  simp [area_form_to_volume_form]
end

/-- Continuous linear map version of `orientation.area_form`, useful for calculus. -/
def area_form' : E →L[ℝ] (E →L[ℝ] ℝ) :=
((↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)))
  ∘ₗ o.area_form).to_continuous_linear_map

@[simp] lemma area_form'_apply (x : E) :
  o.area_form' x = (o.area_form x).to_continuous_linear_map :=
rfl

lemma abs_area_form_le (x y : E) : |ω x y| ≤ ‖x‖ * ‖y‖ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.abs_volume_form_apply_le ![x, y]

lemma area_form_le (x y : E) : ω x y ≤ ‖x‖ * ‖y‖ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.volume_form_apply_le ![x, y]

lemma abs_area_form_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ‖x‖ * ‖y‖ :=
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

lemma area_form_map {F : Type*} [inner_product_space ℝ F] [fact (finrank ℝ F = 2)]
  (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
  (orientation.map (fin 2) φ.to_linear_equiv o).area_form x y = o.area_form (φ.symm x) (φ.symm y) :=
begin
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y],
  { ext i,
    fin_cases i; refl },
  simp [area_form_to_volume_form, volume_form_map, this],
end

/-- The area form is invariant under pullback by a positively-oriented isometric automorphism. -/
lemma area_form_comp_linear_isometry_equiv (φ : E ≃ₗᵢ[ℝ] E)
  (hφ : 0 < (φ.to_linear_equiv : E →ₗ[ℝ] E).det) (x y : E) :
  o.area_form (φ x) (φ y) = o.area_form x y :=
begin
  convert o.area_form_map φ (φ x) (φ y),
  { symmetry,
    rwa ← o.map_eq_iff_det_pos φ.to_linear_equiv at hφ,
    rw [fact.out (finrank ℝ E = 2), fintype.card_fin] },
  { simp },
  { simp }
end

/-- Auxiliary construction for `orientation.right_angle_rotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
@[irreducible] def right_angle_rotation_aux₁ : E →ₗ[ℝ] E :=
let to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
  (inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm in
↑to_dual.symm ∘ₗ ω

@[simp] lemma inner_right_angle_rotation_aux₁_left (x y : E) :
  ⟪o.right_angle_rotation_aux₁ x, y⟫ = ω x y :=
by simp only [right_angle_rotation_aux₁, linear_equiv.trans_symm, linear_equiv.coe_trans,
              linear_equiv.coe_coe, inner_product_space.to_dual_symm_apply, eq_self_iff_true,
              linear_map.coe_to_continuous_linear_map', linear_isometry_equiv.coe_to_linear_equiv,
              linear_map.comp_apply, linear_equiv.symm_symm,
              linear_isometry_equiv.to_linear_equiv_symm]

@[simp] lemma inner_right_angle_rotation_aux₁_right (x y : E) :
  ⟪x, o.right_angle_rotation_aux₁ y⟫ = - ω x y :=
begin
  rw real_inner_comm,
  simp [o.area_form_swap y x],
end

/-- Auxiliary construction for `orientation.right_angle_rotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
def right_angle_rotation_aux₂ : E →ₗᵢ[ℝ] E :=
{ norm_map' := λ x, begin
    dsimp,
    refine le_antisymm _ _,
    { cases eq_or_lt_of_le (norm_nonneg (o.right_angle_rotation_aux₁ x)) with h h,
      { rw ← h,
        positivity },
      refine le_of_mul_le_mul_right _ h,
      rw [← real_inner_self_eq_norm_mul_norm, o.inner_right_angle_rotation_aux₁_left],
      exact o.area_form_le x (o.right_angle_rotation_aux₁ x) },
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
      have hw' : ⟪x, (w:E)⟫ = 0 := submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2,
      have hw : (w:E) ≠ 0 := λ h, hw₀ (submodule.coe_eq_zero.mp h),
      refine le_of_mul_le_mul_right _ (by rwa norm_pos_iff : 0 < ‖(w:E)‖),
      rw ← o.abs_area_form_of_orthogonal hw',
      rw ← o.inner_right_angle_rotation_aux₁_left x w,
      exact abs_real_inner_le_norm (o.right_angle_rotation_aux₁ x) w },
  end,
  .. o.right_angle_rotation_aux₁ }

@[simp] lemma right_angle_rotation_aux₁_right_angle_rotation_aux₁ (x : E) :
  o.right_angle_rotation_aux₁ (o.right_angle_rotation_aux₁ x) = - x :=
begin
  apply ext_inner_left ℝ,
  intros y,
  have : ⟪o.right_angle_rotation_aux₁ y, o.right_angle_rotation_aux₁ x⟫ = ⟪y, x⟫ :=
    linear_isometry.inner_map_map o.right_angle_rotation_aux₂ y x,
  rw [o.inner_right_angle_rotation_aux₁_right, ← o.inner_right_angle_rotation_aux₁_left, this,
    inner_neg_right],
end

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1.  We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
@[irreducible] def right_angle_rotation : E ≃ₗᵢ[ℝ] E :=
linear_isometry_equiv.of_linear_isometry
  o.right_angle_rotation_aux₂
  (-o.right_angle_rotation_aux₁)
  (by ext; simp [right_angle_rotation_aux₂])
  (by ext; simp [right_angle_rotation_aux₂])

local notation `J` := o.right_angle_rotation

@[simp] lemma inner_right_angle_rotation_left (x y : E) : ⟪J x, y⟫ = ω x y :=
begin
  rw right_angle_rotation,
  exact o.inner_right_angle_rotation_aux₁_left x y
end

@[simp] lemma inner_right_angle_rotation_right (x y : E) : ⟪x, J y⟫ = - ω x y :=
begin
  rw right_angle_rotation,
  exact o.inner_right_angle_rotation_aux₁_right x y
end

@[simp] lemma right_angle_rotation_right_angle_rotation (x : E) : J (J x) = - x :=
begin
  rw right_angle_rotation,
  exact o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ x
end

@[simp] lemma right_angle_rotation_symm :
  linear_isometry_equiv.symm J = linear_isometry_equiv.trans J (linear_isometry_equiv.neg ℝ) :=
begin
  rw right_angle_rotation,
  exact linear_isometry_equiv.to_linear_isometry_injective rfl
end

@[simp] lemma inner_right_angle_rotation_self (x : E) : ⟪J x, x⟫ = 0 := by simp

lemma inner_right_angle_rotation_swap (x y : E) : ⟪x, J y⟫ = - ⟪J x, y⟫ := by simp

lemma inner_right_angle_rotation_swap' (x y : E) : ⟪J x, y⟫ = - ⟪x, J y⟫ :=
by simp [o.inner_right_angle_rotation_swap x y]

lemma inner_comp_right_angle_rotation (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
linear_isometry_equiv.inner_map_map J x y

@[simp] lemma area_form_right_angle_rotation_left (x y : E) : ω (J x) y = - ⟪x, y⟫ :=
by rw [← o.inner_comp_right_angle_rotation, o.inner_right_angle_rotation_right, neg_neg]

@[simp] lemma area_form_right_angle_rotation_right (x y : E) : ω x (J y) = ⟪x, y⟫ :=
by rw [← o.inner_right_angle_rotation_left, o.inner_comp_right_angle_rotation]

@[simp] lemma area_form_comp_right_angle_rotation (x y : E) : ω (J x) (J y) = ω x y :=
by simp

@[simp] lemma right_angle_rotation_trans_right_angle_rotation :
  linear_isometry_equiv.trans J J = linear_isometry_equiv.neg ℝ :=
by ext; simp

lemma right_angle_rotation_neg_orientation (x : E) :
  (-o).right_angle_rotation x = - o.right_angle_rotation x :=
begin
  apply ext_inner_right ℝ,
  intros y,
  rw inner_right_angle_rotation_left,
  simp
end

@[simp] lemma right_angle_rotation_trans_neg_orientation :
  (-o).right_angle_rotation = o.right_angle_rotation.trans (linear_isometry_equiv.neg ℝ) :=
linear_isometry_equiv.ext $ o.right_angle_rotation_neg_orientation

lemma right_angle_rotation_map {F : Type*} [inner_product_space ℝ F] [fact (finrank ℝ F = 2)]
  (φ : E ≃ₗᵢ[ℝ] F) (x : F) :
  (orientation.map (fin 2) φ.to_linear_equiv o).right_angle_rotation x
  = φ (o.right_angle_rotation (φ.symm x)) :=
begin
  apply ext_inner_right ℝ,
  intros y,
  rw inner_right_angle_rotation_left,
  transitivity ⟪J (φ.symm x), φ.symm y⟫,
  { simp [o.area_form_map] },
  transitivity ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫,
  { rw φ.inner_map_map },
  { simp },
end

/-- `J` commutes with any positively-oriented isometric automorphism. -/
lemma linear_isometry_equiv_comp_right_angle_rotation (φ : E ≃ₗᵢ[ℝ] E)
  (hφ : 0 < (φ.to_linear_equiv : E →ₗ[ℝ] E).det) (x : E) :
  φ (J x) = J (φ x) :=
begin
  convert (o.right_angle_rotation_map φ (φ x)).symm,
  { simp },
  { symmetry,
    rwa ← o.map_eq_iff_det_pos φ.to_linear_equiv at hφ,
    rw [fact.out (finrank ℝ E = 2), fintype.card_fin] },
end

lemma right_angle_rotation_map' {F : Type*} [inner_product_space ℝ F] [fact (finrank ℝ F = 2)]
  (φ : E ≃ₗᵢ[ℝ] F) :
  (orientation.map (fin 2) φ.to_linear_equiv o).right_angle_rotation
  = (φ.symm.trans o.right_angle_rotation).trans φ :=
linear_isometry_equiv.ext $ o.right_angle_rotation_map φ

/-- `J` commutes with any positively-oriented isometric automorphism. -/
lemma linear_isometry_equiv_comp_right_angle_rotation' (φ : E ≃ₗᵢ[ℝ] E)
  (hφ : 0 < (φ.to_linear_equiv : E →ₗ[ℝ] E).det) :
  linear_isometry_equiv.trans J φ = φ.trans J :=
linear_isometry_equiv.ext $ o.linear_isometry_equiv_comp_right_angle_rotation φ hφ

/-- For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,
`![x, J x]` forms an (orthogonal) basis for `E`. -/
def basis_right_angle_rotation (x : E) (hx : x ≠ 0) : basis (fin 2) ℝ E :=
@basis_of_linear_independent_of_card_eq_finrank ℝ _ _ _ _ _ _ _ ![x, J x]
(linear_independent_of_ne_zero_of_inner_eq_zero (λ i, by { fin_cases i; simp [hx] })
  begin
    intros i j hij,
    fin_cases i; fin_cases j,
    { simpa },
    { simp },
    { simp },
    { simpa }
  end)
(fact.out (finrank ℝ E = 2)).symm

@[simp] lemma coe_basis_right_angle_rotation (x : E) (hx : x ≠ 0) :
  ⇑(o.basis_right_angle_rotation x hx) = ![x, J x] :=
coe_basis_of_linear_independent_of_card_eq_finrank _ _

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. (See
`orientation.inner_mul_inner_add_area_form_mul_area_form` for the "applied" form.)-/
lemma inner_mul_inner_add_area_form_mul_area_form' (a x : E) :
  ⟪a, x⟫ • @innerₛₗ ℝ _ _ _ a + ω a x • ω a = ‖a‖ ^ 2 • @innerₛₗ ℝ _ _ _ x :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  apply (o.basis_right_angle_rotation a ha).ext,
  intros i,
  fin_cases i,
  { simp only [real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply,
      linear_map.smul_apply, linear_map.add_apply, matrix.cons_val_zero,
      o.coe_basis_right_angle_rotation, o.area_form_apply_self, real_inner_comm],
    ring },
  { simp only [real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply,
      linear_map.smul_apply, neg_inj, linear_map.add_apply, matrix.cons_val_one, matrix.head_cons,
      o.coe_basis_right_angle_rotation, o.area_form_right_angle_rotation_right,
      o.area_form_apply_self, o.inner_right_angle_rotation_right],
    rw o.area_form_swap,
    ring, }
end

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. -/
lemma inner_mul_inner_add_area_form_mul_area_form (a x y : E) :
  ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫ :=
congr_arg (λ f : E →ₗ[ℝ] ℝ, f y) (o.inner_mul_inner_add_area_form_mul_area_form' a x)

lemma inner_sq_add_area_form_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 :=
by simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_area_form_mul_area_form a b b

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. (See
`orientation.inner_mul_area_form_sub` for the "applied" form.) -/
lemma inner_mul_area_form_sub' (a x : E) :
  ⟪a, x⟫ • ω a - ω a x • @innerₛₗ ℝ _ _ _ a = ‖a‖ ^ 2 • ω x :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  apply (o.basis_right_angle_rotation a ha).ext,
  intros i,
  fin_cases i,
  { simp only [o.coe_basis_right_angle_rotation, o.area_form_apply_self, o.area_form_swap a x,
      real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply, linear_map.sub_apply,
      linear_map.smul_apply, matrix.cons_val_zero],
    ring },
  { simp only [o.area_form_right_angle_rotation_right, o.area_form_apply_self,
      o.coe_basis_right_angle_rotation, o.inner_right_angle_rotation_right,
      real_inner_self_eq_norm_sq, real_inner_comm, algebra.id.smul_eq_mul, innerₛₗ_apply,
      linear_map.smul_apply, linear_map.sub_apply, matrix.cons_val_one, matrix.head_cons],
  ring},
end

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. -/
lemma inner_mul_area_form_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y :=
congr_arg (λ f : E →ₗ[ℝ] ℝ, f y) (o.inner_mul_area_form_sub' a x)

lemma nonneg_inner_and_area_form_eq_zero_iff_same_ray (x y : E) :
  0 ≤ ⟪x, y⟫ ∧ ω x y = 0 ↔ same_ray ℝ x y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  split,
  { let a : ℝ := (o.basis_right_angle_rotation x hx).repr y 0,
    let b : ℝ := (o.basis_right_angle_rotation x hx).repr y 1,
    suffices : 0 ≤ a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 → same_ray ℝ x (a • x + b • J x),
    { rw ← (o.basis_right_angle_rotation x hx).sum_repr y,
      simp only [fin.sum_univ_succ, coe_basis_right_angle_rotation, matrix.cons_val_zero,
        fin.succ_zero_eq_one', fintype.univ_of_is_empty, finset.sum_empty, o.area_form_apply_self,
        map_smul, map_add, map_zero, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, inner_zero_right, linear_map.add_apply, matrix.cons_val_one,
        matrix.head_cons, algebra.id.smul_eq_mul, o.area_form_right_angle_rotation_right, mul_zero,
        add_zero, zero_add, neg_zero, o.inner_right_angle_rotation_right, o.area_form_apply_self,
        real_inner_self_eq_norm_sq],
      exact this },
    rintros ⟨ha, hb⟩,
    have hx' : 0 < ‖x‖ := by simpa using hx,
    have ha' : 0 ≤ a := nonneg_of_mul_nonneg_left ha (by positivity),
    have hb' : b = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero 2 hx'.ne') hb,
    simpa [hb'] using same_ray_nonneg_smul_right x ha' },
  { intros h,
    obtain ⟨r, hr, rfl⟩ := h.exists_nonneg_left hx,
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, linear_map.map_smulₛₗ,
      area_form_apply_self, algebra.id.smul_eq_mul, mul_zero, eq_self_iff_true, and_true],
    positivity },
end

/-- A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its
real part is the inner product and its imaginary part is `orientation.area_form`.

On `ℂ` with the standard orientation, `kahler w z = conj w * z`; see `complex.kahler`. -/
def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
(linear_map.llcomp ℝ E ℝ ℂ complex.of_real_clm) ∘ₗ (@innerₛₗ ℝ E _ _)
+ (linear_map.llcomp ℝ E ℝ ℂ ((linear_map.lsmul ℝ ℂ).flip complex.I)) ∘ₗ ω

lemma kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • complex.I := rfl

lemma kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) :=
begin
  simp only [kahler_apply_apply],
  rw [real_inner_comm, area_form_swap],
  simp,
end

@[simp] lemma kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 :=
by simp [kahler_apply_apply, real_inner_self_eq_norm_sq]

@[simp] lemma kahler_right_angle_rotation_left (x y : E) :
  o.kahler (J x) y = - complex.I * o.kahler x y :=
begin
  simp only [o.area_form_right_angle_rotation_left, o.inner_right_angle_rotation_left,
    o.kahler_apply_apply, complex.of_real_neg, complex.real_smul],
  linear_combination ω x y * complex.I_sq,
end

@[simp] lemma kahler_right_angle_rotation_right (x y : E) :
  o.kahler x (J y) = complex.I * o.kahler x y :=
begin
  simp only [o.area_form_right_angle_rotation_right, o.inner_right_angle_rotation_right,
    o.kahler_apply_apply, complex.of_real_neg, complex.real_smul],
  linear_combination - ω x y * complex.I_sq,
end

@[simp] lemma kahler_comp_right_angle_rotation (x y : E) : o.kahler (J x) (J y) = o.kahler x y :=
begin
  simp only [kahler_right_angle_rotation_left, kahler_right_angle_rotation_right],
  linear_combination - o.kahler x y * complex.I_sq,
end

@[simp] lemma kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) :=
by simp [kahler_apply_apply]

lemma kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y :=
begin
  transitivity (↑(‖a‖ ^ 2) : ℂ) * o.kahler x y,
  { ext,
    { simp only [o.kahler_apply_apply, complex.add_im, complex.add_re, complex.I_im, complex.I_re,
        complex.mul_im, complex.mul_re, complex.of_real_im, complex.of_real_re, complex.real_smul],
      rw [real_inner_comm a x, o.area_form_swap x a],
      linear_combination o.inner_mul_inner_add_area_form_mul_area_form a x y },
    { simp only [o.kahler_apply_apply, complex.add_im, complex.add_re, complex.I_im, complex.I_re,
        complex.mul_im, complex.mul_re, complex.of_real_im, complex.of_real_re, complex.real_smul],
      rw [real_inner_comm a x, o.area_form_swap x a],
      linear_combination o.inner_mul_area_form_sub a x y } },
  { norm_cast },
end

lemma norm_sq_kahler (x y : E) : complex.norm_sq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 :=
by simpa [kahler_apply_apply, complex.norm_sq, sq] using o.inner_sq_add_area_form_sq x y

lemma abs_kahler (x y : E) : complex.abs (o.kahler x y) = ‖x‖ * ‖y‖ :=
begin
  rw [← sq_eq_sq, complex.sq_abs],
  { linear_combination o.norm_sq_kahler x y },
  { positivity },
  { positivity }
end

lemma norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by simpa using o.abs_kahler x y

lemma eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 :=
begin
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm,
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

lemma kahler_map {F : Type*} [inner_product_space ℝ F] [fact (finrank ℝ F = 2)]
  (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
  (orientation.map (fin 2) φ.to_linear_equiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) :=
by simp [kahler_apply_apply, area_form_map]

/-- The bilinear map `kahler` is invariant under pullback by a positively-oriented isometric
automorphism. -/
lemma kahler_comp_linear_isometry_equiv (φ : E ≃ₗᵢ[ℝ] E)
  (hφ : 0 < (φ.to_linear_equiv : E →ₗ[ℝ] E).det) (x y : E) :
  o.kahler (φ x) (φ y) = o.kahler x y :=
by simp [kahler_apply_apply, o.area_form_comp_linear_isometry_equiv φ hφ]

end orientation

namespace complex

local attribute [instance] complex.finrank_real_complex_fact

@[simp] protected lemma area_form (w z : ℂ) : complex.orientation.area_form w z = (conj w * z).im :=
begin
  let o := complex.orientation,
  simp only [o.area_form_to_volume_form, o.volume_form_robust complex.orthonormal_basis_one_I rfl,
    basis.det_apply, matrix.det_fin_two, basis.to_matrix_apply,to_basis_orthonormal_basis_one_I,
    matrix.cons_val_zero, coe_basis_one_I_repr, matrix.cons_val_one, matrix.head_cons, mul_im,
    conj_re, conj_im],
  ring,
end

@[simp] protected lemma right_angle_rotation (z : ℂ) :
  complex.orientation.right_angle_rotation z = I * z :=
begin
  apply ext_inner_right ℝ,
  intros w,
  rw orientation.inner_right_angle_rotation_left,
  simp only [complex.area_form, complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im],
  ring,
end

@[simp] protected lemma kahler (w z : ℂ) :
  complex.orientation.kahler w z = conj w * z :=
begin
  rw orientation.kahler_apply_apply,
  ext1; simp,
end

end complex

namespace orientation

local notation `ω` := o.area_form
local notation `J` := o.right_angle_rotation

open complex

/-- The area form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
lemma area_form_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x y : E) :
  ω x y = (conj (f x) * f y).im :=
begin
  rw [← complex.area_form, ← hf, o.area_form_map],
  simp,
end

/-- The rotation by 90 degrees on an oriented real inner product space of dimension 2 can be
evaluated in terms of a complex-number representation of the space. -/
lemma right_angle_rotation_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x : E) :
  f (J x) = I * f x :=
begin
  rw [← complex.right_angle_rotation, ← hf, o.right_angle_rotation_map],
  simp,
end

/-- The Kahler form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
lemma kahler_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x y : E) :
  o.kahler x y = conj (f x) * f y :=
begin
  rw [← complex.kahler, ← hf, o.kahler_map],
  simp,
end

end orientation
