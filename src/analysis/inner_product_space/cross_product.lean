/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation

/-! # The cross-product on an oriented real inner product space of dimension three

This file gives a construction of the cross-product on an oriented real inner product space `E` of
dimension three.

## Implementation notes

Notation `×₃` for `orientation.cross_product` should be defined locally in each file which uses it,
since otherwise one would need a more cumbersome notation which mentions the orientation explicitly
(something like `×₃[o]`).  Write
```
local infixl ` ×₃ `: 74 := o.cross_product
```

## TODO

`matrix.cross_product` is a construction in co-ordinates of the cross-product on `R`^3, for `R` a
commutative ring.  Either that construction should be superseded by this basis-free one (which still
involves a loss of generality, in moving from a general commutative ring to just `ℝ`) or, if the two
constructions will co-exist, there should be lemmas relating the two constructions.
-/

noncomputable theory

open_locale real_inner_product_space
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables {E : Type*} [inner_product_space ℝ E] [fact (finrank ℝ E = 3)]
  (o : orientation ℝ E (fin 3))

include o

namespace orientation

/-- The cross-product on an oriented real inner product space of dimension 3, considered as a
linear map from `E` to `E →ₗ[ℝ] E`, or equivalently a bilinear map from `E × E` to `E`.

The cross-product is constructed here using the volume form, a 3-form on `E` determined uniquely by
the orientation and inner product structure. The partial evaluation of the volume form o on `u` and
`v` gives an element o(u, v, ⬝) of the dual of `E`.  This can then be identified with `E` itself
using the canonical isometry (induced by the inner product) between `E` and its dual.

See `matrix.cross_product` for a construction of the cross-product in co-ordinates. -/
@[irreducible] def cross_product : E →ₗ[ℝ] E →ₗ[ℝ] E :=
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
  let u : alternating_map ℝ E ℝ (fin 2) →ₗ[ℝ] E →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 1)) _ y') ∘ₗ
      alternating_map.curry_left_linear_map,
  exact u ∘ₗ (alternating_map.curry_left_linear_map o.volume_form),
end

local infixl ` ×₃ `: 74 := o.cross_product

/-- Defining property of the cross-product: for vectors `u`, `v`, `w`, the inner product of u × v
with w is equal to o(u, v, w), where -/
lemma inner_cross_product_apply (u v w : E) : ⟪u ×₃ v, w⟫ = o.volume_form ![u, v, w] :=
by simp only [cross_product, linear_equiv.trans_symm, linear_equiv.symm_symm,
  linear_isometry_equiv.to_linear_equiv_symm, alternating_map.curry_left_linear_map_apply,
  linear_map.coe_comp, function.comp_app, linear_map.llcomp_apply,
  linear_equiv.coe_coe, linear_equiv.trans_apply, linear_isometry_equiv.coe_to_linear_equiv,
  linear_isometry_equiv.norm_map, submodule.coe_norm,
  inner_product_space.to_dual_symm_apply, alternating_map.curry_left_apply_apply,
  alternating_map.const_linear_equiv_of_is_empty_symm_apply,
  eq_self_iff_true, linear_map.coe_to_continuous_linear_map', matrix.zero_empty]

/-- The cross-product is antisymmetric: `x ×₃ y = - (y ×₃ x)`. -/
lemma cross_product_swap (x y : E) : x ×₃ y = - (y ×₃ x) :=
begin
  apply ext_inner_right ℝ,
  intros z,
  rw [inner_neg_left, o.inner_cross_product_apply, o.inner_cross_product_apply],
  convert o.volume_form.map_swap ![y, x, z] (_ : (0 : fin 3) ≠ 1),
  { ext i,
    fin_cases i; refl },
  { norm_num }
end

/-- The cross-product is antisymmetric: the cross-product of a vector with itself is 0. -/
lemma cross_product_apply_self (v : E) : v ×₃ v = 0 :=
begin
  apply ext_inner_right ℝ,
  intros w,
  rw [inner_cross_product_apply, inner_zero_left],
  refine o.volume_form.map_eq_zero_of_eq ![v, v, w] _ (_ : (0 : fin 3) ≠ 1),
  { simp },
  { norm_num }
end

/-- The cross-product of `u` and `v` is orthogonal to `u`. -/
lemma inner_cross_product_apply_self (u v : E) : ⟪u ×₃ v, u⟫ = 0 :=
begin
  rw o.inner_cross_product_apply u v u,
  refine o.volume_form.map_eq_zero_of_eq ![u, v, u] _ (_ : (0 : fin 3) ≠ 2),
  { simp },
  { norm_num }
end

/-- The cross-product of `u` and `v` is orthogonal to `v`. -/
lemma inner_cross_product_apply_apply_self (u v : E) : ⟪u ×₃ v, v⟫ = 0 :=
by rw [cross_product_swap, inner_neg_left, inner_cross_product_apply_self, neg_zero]

/-- The map `cross_product`, upgraded from linear to continuous-linear; useful for calculus. -/
def cross_product' : E →L[ℝ] (E →L[ℝ] E) :=
(↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E))
  ∘ₗ (o.cross_product)).to_continuous_linear_map

@[simp] lemma cross_product'_apply (v : E) :
  o.cross_product' v = (o.cross_product v).to_continuous_linear_map :=
rfl

/-- The norm of the cross-product of `u` and `v` is bounded by the product of the norms of `u` and
`v`. -/
lemma norm_cross_product_le (u v : E) : ∥u ×₃ v∥ ≤ ∥u∥ * ∥v∥ :=
begin
  cases eq_or_lt_of_le (norm_nonneg (u ×₃ v)) with h h,
  { rw ← h,
    positivity },
  refine le_of_mul_le_mul_right _ h,
  rw ← real_inner_self_eq_norm_mul_norm,
  simpa only [inner_cross_product_apply, fin.mk_zero, fin.prod_univ_succ, finset.card_singleton,
    finset.prod_const, fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ,
    matrix.cons_val_zero, mul_assoc, nat.nat_zero_eq_zero, pow_one, submodule.coe_norm]
    using o.volume_form_apply_le ![u, v, u ×₃ v]
end

/-- For orthogonal vectors `u` and `v`, the norm of the cross-product of `u` and `v` is the product
of the norms of `u` and `v`. -/
lemma norm_cross_product (u : E) (v : (ℝ ∙ u)ᗮ) : ∥u ×₃ v∥ = ∥u∥ * ∥v∥ :=
begin
  classical,
  refine le_antisymm (o.norm_cross_product_le u v) _,
  let K : submodule ℝ E := submodule.span ℝ ({u, v} : set E),
  haveI : nontrivial Kᗮ,
  { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
    have : finrank ℝ K ≤ finset.card {u, (v:E)},
    { simpa [set.to_finset_singleton] using finrank_span_le_card ({u, v} : set E) },
    have : finset.card {u, (v:E)} ≤ finset.card {(v:E)} + 1 := finset.card_insert_le u {v},
    have : finset.card {(v:E)} = 1 := finset.card_singleton (v:E),
    have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal,
    have : finrank ℝ E = 3 := fact.out _,
    linarith },
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0,
  have hw' : (w:E) ≠ 0 := λ h, hw (submodule.coe_eq_zero.mp h),
  have H : pairwise (λ i j, ⟪![u, v, w] i, ![u, v, w] j⟫ = 0),
  { intros i j hij,
    have h1 : ⟪u, v⟫ = 0 := v.2 _ (submodule.mem_span_singleton_self _),
    have h2 : ⟪(v:E), w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    have h3 : ⟪u, w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    fin_cases i; fin_cases j; norm_num at hij; simp [h1, h2, h3]; rw real_inner_comm; assumption },
  refine le_of_mul_le_mul_right _ (by rwa norm_pos_iff : 0 < ∥w∥),
  -- Cauchy-Schwarz inequality for `u ×₃ v` and `w`
  simpa only [inner_cross_product_apply, o.abs_volume_form_apply_of_pairwise_orthogonal H,
    inner_cross_product_apply, fin.mk_zero, fin.prod_univ_succ, finset.card_singleton,
    finset.prod_const, fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ,
    matrix.cons_val_zero, nat.nat_zero_eq_zero, pow_one, mul_assoc]
    using abs_real_inner_le_norm (u ×₃ v) w,
end

lemma isometry_on_cross_product (u : metric.sphere (0:E) 1) (v : (ℝ ∙ (u:E))ᗮ) : ∥u ×₃ v∥ = ∥v∥ :=
by simp [norm_cross_product]

end orientation
