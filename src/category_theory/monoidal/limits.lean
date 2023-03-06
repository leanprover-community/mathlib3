/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functorial
import category_theory.monoidal.functor_category
import category_theory.limits.has_limits

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `lim_lax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `lim_lax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.
-/

open category_theory
open category_theory.monoidal_category

namespace category_theory.limits

universes v u

noncomputable theory

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C] [has_limits C]

instance limit_functorial : functorial (λ F : J ⥤ C, limit F) := { ..limits.lim }

@[simp] lemma limit_functorial_map {F G : J ⥤ C} (α : F ⟶ G) :
  map (λ F : J ⥤ C, limit F) α = limits.lim.map α := rfl

variables  [monoidal_category.{v} C]

@[simps]
instance limit_lax_monoidal : lax_monoidal (λ F : J ⥤ C, limit F) :=
{ ε := limit.lift _ { X := _, π := { app := λ j, 𝟙 _, } },
  μ := λ F G, limit.lift (F ⊗ G)
    { X := limit F ⊗ limit G,
      π :=
      { app := λ j, limit.π F j ⊗ limit.π G j,
        naturality' := λ j j' f,
        begin
          dsimp,
          simp only [category.id_comp, ←tensor_comp, limit.w],
        end, } },
  μ_natural' := λ X Y X' Y' f g,
  begin
    ext, dsimp,
    simp only [limit.lift_π, cones.postcompose_obj_π, monoidal.tensor_hom_app, limit.lift_map,
      nat_trans.comp_app, category.assoc, ←tensor_comp, lim_map_π],
  end,
  associativity' := λ X Y Z,
  begin
    ext, dsimp,
    simp only [limit.lift_π, cones.postcompose_obj_π, monoidal.associator_hom_app, limit.lift_map,
      nat_trans.comp_app, category.assoc],
    slice_lhs 2 2 { rw [←tensor_id_comp_id_tensor], },
    slice_lhs 1 2 { rw [←comp_tensor_id, limit.lift_π], dsimp, },
    slice_lhs 1 2 { rw [tensor_id_comp_id_tensor], },
    conv_lhs { rw [associator_naturality], },
    conv_rhs { rw [←id_tensor_comp_tensor_id (limit.π (Y ⊗ Z) j)], },
    slice_rhs 2 3 { rw [←id_tensor_comp, limit.lift_π], dsimp, },
    dsimp, simp,
  end,
  left_unitality' := λ X,
  begin
    ext, dsimp,
    simp,
    conv_rhs { rw [←tensor_id_comp_id_tensor (limit.π X j)], },
    slice_rhs 1 2 { rw [←comp_tensor_id], erw [limit.lift_π], dsimp, },
    slice_rhs 2 3 { rw [left_unitor_naturality], },
    simp,
  end,
  right_unitality' := λ X,
  begin
    ext, dsimp,
    simp,
    conv_rhs { rw [←id_tensor_comp_tensor_id _ (limit.π X j)], },
    slice_rhs 1 2 { rw [←id_tensor_comp], erw [limit.lift_π], dsimp, },
    slice_rhs 2 3 { rw [right_unitor_naturality], },
    simp,
  end, }

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def lim_lax : lax_monoidal_functor (J ⥤ C) C := lax_monoidal_functor.of (λ F : J ⥤ C, limit F)

@[simp] lemma lim_lax_obj (F : J ⥤ C) : lim_lax.obj F = limit F := rfl

lemma lim_lax_obj' (F : J ⥤ C) : lim_lax.obj F = lim.obj F := rfl

@[simp] lemma lim_lax_map {F G : J ⥤ C} (α : F ⟶ G) : lim_lax.map α = lim.map α := rfl

@[simp] lemma lim_lax_ε :
  (@lim_lax J _ C _ _ _).ε = limit.lift _ { X := _, π := { app := λ j, 𝟙 _, } } := rfl

@[simp] lemma lim_lax_μ (F G : J ⥤ C) :
  (@lim_lax J _ C _ _ _).μ F G = limit.lift (F ⊗ G)
    { X := limit F ⊗ limit G,
      π :=
      { app := λ j, limit.π F j ⊗ limit.π G j,
        naturality' := λ j j' f,
        begin
          dsimp,
          simp only [category.id_comp, ←tensor_comp, limit.w],
        end, } } := rfl

end category_theory.limits
