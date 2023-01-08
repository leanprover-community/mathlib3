/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import linear_algebra.affine_space.affine_subspace

/-!
# Affine map restrictions

This file defines restrictions of affine maps.

## Main definitions

* The domain and codomain of an affine map can be restricted using
  `affine_map.restrict`.

## Main theorems

* The associated linear map of the restriction is the restriction of the
  linear map associated to the original affine map.
* The restriction is injective if the original map is injective.
* The restriction in surjective if the codomain is the image of the domain.
-/

variables {k V₁ P₁ V₂ P₂ : Type*} [ring k]
  [add_comm_group V₁] [add_comm_group V₂]
  [module k V₁] [module k V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]

include V₁ V₂

/- not an instance because it loops with `nonempty` -/
lemma affine_subspace.nonempty_map {E : affine_subspace k P₁} [Ene : nonempty E]
  {φ : P₁ →ᵃ[k] P₂} : nonempty (E.map φ) :=
begin
  obtain ⟨x, hx⟩ := id Ene,
  refine ⟨⟨φ x, affine_subspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩,
end

local attribute [instance, nolint fails_quickly] affine_subspace.nonempty_map
local attribute [instance, nolint fails_quickly] affine_subspace.to_add_torsor

/-- Restrict domain and codomain of an affine map to the given subspaces. -/
def affine_map.restrict
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) : E →ᵃ[k] F :=
begin
  refine ⟨_, _, _⟩,
  { exact λ x, ⟨φ x, hEF $ affine_subspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩ },
  { refine φ.linear.restrict (_ : E.direction ≤ F.direction.comap φ.linear),
    rw [←submodule.map_le_iff_le_comap, ←affine_subspace.map_direction],
    exact affine_subspace.direction_le hEF },
  { intros p v,
    simp only [subtype.ext_iff, subtype.coe_mk, affine_subspace.coe_vadd],
    apply affine_map.map_vadd },
end

lemma affine_map.restrict.coe_apply
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) (x : E) :
  ↑(φ.restrict hEF x) = φ x := rfl

lemma affine_map.restrict.linear_aux
  {φ : P₁ →ᵃ[k] P₂} {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  (hEF : E.map φ ≤ F) : E.direction ≤ F.direction.comap φ.linear :=
begin
  rw [←submodule.map_le_iff_le_comap, ←affine_subspace.map_direction],
  exact affine_subspace.direction_le hEF,
end

lemma affine_map.restrict.linear
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
  (φ.restrict hEF).linear = φ.linear.restrict (affine_map.restrict.linear_aux hEF) := rfl

lemma affine_map.restrict.injective
  {φ : P₁ →ᵃ[k] P₂}
  (hφ : function.injective φ) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
  function.injective (affine_map.restrict φ hEF) :=
begin
  intros x y h,
  simp only [subtype.ext_iff, subtype.coe_mk, affine_map.restrict.coe_apply] at h ⊢,
  exact hφ h,
end

lemma affine_map.restrict.surjective
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F] (h : E.map φ = F) :
  function.surjective (affine_map.restrict φ (le_of_eq h)) :=
begin
  rintro ⟨x, hx : x ∈ F⟩,
  rw [←h, affine_subspace.mem_map] at hx,
  obtain ⟨y, hy, rfl⟩ := hx,
  exact ⟨⟨y, hy⟩, rfl⟩,
end

lemma affine_map.restrict.bijective
  {E : affine_subspace k P₁} [nonempty E]
  {φ : P₁ →ᵃ[k] P₂} (hφ : function.injective φ) :
  function.bijective (φ.restrict (le_refl (E.map φ))) :=
⟨affine_map.restrict.injective hφ _, affine_map.restrict.surjective _ rfl⟩
