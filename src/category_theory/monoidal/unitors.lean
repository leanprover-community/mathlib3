/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

We prove that the left and right unitors `𝟙_ C ⊗ 𝟙_ C ⟶ 𝟙_ C` are equal.
This is surprisingly difficult (indeed, in early definitions of monoidal categories it
was an additional axiom).
This proof follows a commutative diagram drawn by Jamie Vicary.
-/

import category_theory.monoidal.category
import tactic.slice

universes v u

namespace category_theory
open category_theory.category
open category_theory.monoidal_category

variables {C : Sort u} [𝒞 : monoidal_category.{v} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

namespace unitors_equal

lemma cells_1_2 : (ρ_ (𝟙_ C)).hom = (λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by rw [left_unitor_conjugation]

lemma cells_4 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).hom)) = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv :=
by rw [←left_unitor_inv_naturality, iso.hom_inv_id]

lemma cells_4' :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) :=
by rw [←assoc, ←cells_4, assoc, id_tensor_comp, iso.hom_inv_id, tensor_id, comp_id]

lemma cells_3_4 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv) :=
by rw [cells_4', ←assoc, iso.hom_inv_id, id_comp]

lemma cells_1_4 :
(ρ_ (𝟙_ C)).hom  = ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv))  ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
begin
  rw [←cells_3_4],
  conv_lhs { rw [cells_1_2] },
end

lemma cells_6 :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).hom = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv :=
by rw [right_unitor_naturality, iso.hom_inv_id]

lemma cells_6' :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv :=
by {rw [←assoc, ←cells_6, assoc, iso.hom_inv_id, comp_id], }

lemma cells_5_6 : ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C ⊗ 𝟙_ C)).inv :=
by rw [cells_6', ←assoc, iso.hom_inv_id, id_comp]

lemma cells_7 : ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) = ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom :=
by simp only [triangle_assoc_comp_right_inv, tensor_left_iff]

lemma cells_1_7 :
(ρ_ (𝟙_ C)).hom = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
begin
  conv_lhs { rw [cells_1_4] },
  conv_lhs { congr, rw [cells_7] },
  conv_lhs { congr, congr, rw [cells_5_6] },
  conv_rhs { rw [←assoc] }
end

lemma cells_8 : (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom = (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv ≫ ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom :=
by rw [right_unitor_conjugation].

lemma cells_14 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) :=
by rw [right_unitor_inv_naturality]

lemma cells_9 : ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) = (α_ ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C) (𝟙_ C)).hom ≫ (α_ (𝟙_ C) (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv) ≫ (α_ (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C)).inv  :=
begin
  slice_rhs 1 2 { rw ←(monoidal_category.pentagon C (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C)) },
  slice_rhs 3 4 { rw [id_tensor_comp, iso.hom_inv_id], },
  simp,
end

lemma cells_10_13 : ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) ≫ (α_ ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C) (𝟙_ C)).hom ≫ (α_ (𝟙_ C) (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv) ≫ (α_ (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C)).inv = ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C)) :=
begin
 slice_lhs 1 2 { simp, },
 slice_lhs 1 2 { rw [←tensor_id, associator_naturality], },
 slice_lhs 2 3 { rw [id_tensor_comp], simp, },
 slice_lhs 1 2 { rw ←associator_naturality, },
 simp,
end

lemma cells_9_13 : ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) ≫ ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) = ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C)) :=
begin
  rw [cells_9, ←cells_10_13]
end

lemma cells_15 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) = 𝟙 _ :=
begin
  slice_lhs 1 2 { rw [←right_unitor_inv_naturality] },
  slice_lhs 2 3 { rw [iso.inv_hom_id] },
  rw [id_comp, id_tensor_comp, iso.inv_hom_id, tensor_id],
end

end unitors_equal

open unitors_equal

@[simp] lemma unitors_equal : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom :=
begin
  rw cells_1_7,
  rw cells_8,
  slice_lhs 1 2 { rw cells_14 },
  slice_lhs 2 3 { rw cells_9_13 },
  slice_lhs 1 4 { rw cells_15 },
  rw id_comp,
end

end category_theory
