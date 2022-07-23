/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import category_theory.closed.monoidal
import category_theory.monoidal.functor_category

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

(Using the pointwise monoidal structure on the functor category.)
-/

noncomputable theory

open category_theory
open category_theory.monoidal_category

namespace category_theory.monoidal_closed

variables {C D : Type*} [groupoid D] [category C] [monoidal_category C] [monoidal_closed C]

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps] def functor_closed_ihom (F : D ⥤ C) : (D ⥤ C) ⥤ (D ⥤ C) :=
((whiskering_right₂ D Cᵒᵖ C C).obj internal_hom).obj (groupoid.inv_functor D ⋙ F.op)

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The unit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def functor_closed_unit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ (tensor_left F) ⋙ (functor_closed_ihom F) :=
{ app := λ G,
  { app := λ X, (ihom.coev (F.obj X)).app (G.obj X),
    naturality' := begin
      intros X Y f,
      dsimp,
      simp only [ihom.coev_naturality, functor_closed_ihom_obj_map, monoidal.tensor_obj_map],
      dsimp,
      rw [coev_app_comp_pre_app_assoc, ←functor.map_comp],
      simp,
    end } }

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The counit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def functor_closed_counit (F : D ⥤ C) : (functor_closed_ihom F) ⋙ (tensor_left F) ⟶ 𝟭 (D ⥤ C) :=
{ app := λ G,
  { app := λ X, (ihom.ev (F.obj X)).app (G.obj X),
    naturality' := begin
      intros X Y f,
      dsimp,
      simp only [functor_closed_ihom_obj_map, pre_comm_ihom_map],
      rw [←tensor_id_comp_id_tensor, id_tensor_comp],
      simp,
    end } }

/-- If `C` is a monoidal closed category and `D` is groupoid, then every functor `F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure. -/
@[simps] instance functor_closed (F : D ⥤ C) : closed F :=
{ is_adj :=
  { right := functor_closed_ihom F,
    adj := adjunction.mk_of_unit_counit
    { unit := functor_closed_unit F,
      counit := functor_closed_counit F } } }

/-- If `C` is a monoidal closed category and `D` is groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps] instance functor_category : monoidal_closed (D ⥤ C) :=
{ closed' := by apply_instance }

end category_theory.monoidal_closed
