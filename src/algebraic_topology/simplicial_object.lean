/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_topology.simplex_category
import category_theory.category.ulift
import category_theory.limits.functor_category
import category_theory.opposites
import category_theory.adjunction.limits

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `simplex_category`.
-/

open opposite
open category_theory
open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[derive category, nolint has_inhabited_instance]
def simplicial_object := simplex_categoryᵒᵖ ⥤ C

namespace simplicial_object

instance {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object C) :=
let E : (simplex_categoryᵒᵖ ⥤ C) ≌ (ulift.{v} simplex_category)ᵒᵖ ⥤ C :=
  ulift.equivalence.op.congr_left in
  adjunction.has_limits_of_shape_of_equivalence E.functor

instance [has_limits C] : has_limits (simplicial_object C) :=
let E : (simplex_categoryᵒᵖ ⥤ C) ≌ (ulift.{v} simplex_category)ᵒᵖ ⥤ C :=
  ulift.equivalence.op.congr_left in
  adjunction.has_limits_of_equivalence E.functor

instance {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object C) :=
let E : (simplex_categoryᵒᵖ ⥤ C) ≌ (ulift.{v} simplex_category)ᵒᵖ ⥤ C :=
  ulift.equivalence.op.congr_left in
  adjunction.has_colimits_of_shape_of_equivalence E.functor

instance [has_colimits C] : has_colimits (simplicial_object C) :=
let E : (simplex_categoryᵒᵖ ⥤ C) ≌ (ulift.{v} simplex_category)ᵒᵖ ⥤ C :=
  ulift.equivalence.op.congr_left in
  adjunction.has_colimits_of_equivalence E.functor

variables {C} (X : simplicial_object C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : fin (n+2)) : X.obj (op (n+1 : ℕ)) ⟶ X.obj (op n) :=
X.map (simplex_category.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : fin (n+1)) : X.obj (op n) ⟶ X.obj (op (n+1 : ℕ)) :=
X.map (simplex_category.σ i).op


/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X.obj (op n) ≅ X.obj (op m) :=
X.map_iso (eq_to_iso (by rw h))

@[simp] lemma eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
by { ext, simp [eq_to_iso], }


/-- The generic case of the first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ H] }

/-- The special case of the first simplicial identity -/
lemma δ_comp_δ_self {n} {i : fin (n+2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ_self] }

/-- The second simplicial identity -/
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_le H] }

/-- The first part of the third simplicial identity -/
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_self, op_id, X.map_id],
end

/-- The second part of the third simplicial identity -/
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_succ, op_id, X.map_id],
end

/-- The fourth simplicial identity -/
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_gt H] }

/-- The fifth simplicial identity -/
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.σ_comp_σ H] }

end simplicial_object

end category_theory
