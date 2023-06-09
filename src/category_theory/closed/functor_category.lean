/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import category_theory.closed.monoidal
import category_theory.monoidal.functor_category

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

(Using the pointwise monoidal structure on the functor category.)
-/

noncomputable theory

open category_theory
open category_theory.monoidal_category
open category_theory.monoidal_closed

namespace category_theory.functor

variables {C D : Type*} [groupoid D] [category C] [monoidal_category C] [monoidal_closed C]

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps] def closed_ihom (F : D ⥤ C) : (D ⥤ C) ⥤ (D ⥤ C) :=
((whiskering_right₂ D Cᵒᵖ C C).obj internal_hom).obj (groupoid.inv_functor D ⋙ F.op)

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The unit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closed_unit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ (tensor_left F) ⋙ (closed_ihom F) :=
{ app := λ G,
  { app := λ X, (ihom.coev (F.obj X)).app (G.obj X),
    naturality' := begin
      intros X Y f,
      dsimp,
      simp only [ihom.coev_naturality, closed_ihom_obj_map, monoidal.tensor_obj_map],
      dsimp,
      rw [coev_app_comp_pre_app_assoc, ←functor.map_comp],
      simp,
    end } }

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The counit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closed_counit (F : D ⥤ C) : (closed_ihom F) ⋙ (tensor_left F) ⟶ 𝟭 (D ⥤ C) :=
{ app := λ G,
  { app := λ X, (ihom.ev (F.obj X)).app (G.obj X),
    naturality' := begin
      intros X Y f,
      dsimp,
      simp only [closed_ihom_obj_map, pre_comm_ihom_map],
      rw [←tensor_id_comp_id_tensor, id_tensor_comp],
      simp,
    end } }

/-- If `C` is a monoidal closed category and `D` is groupoid, then every functor `F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure. -/
@[simps] instance closed (F : D ⥤ C) : closed F :=
{ is_adj :=
  { right := closed_ihom F,
    adj := adjunction.mk_of_unit_counit
    { unit := closed_unit F,
      counit := closed_counit F } } }

/-- If `C` is a monoidal closed category and `D` is groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps] instance monoidal_closed : monoidal_closed (D ⥤ C) :=
{ closed' := by apply_instance }

lemma ihom_map (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H) :
  (ihom F).map f = (closed_ihom F).map f := rfl

lemma ihom_ev_app (F G : D ⥤ C) :
  (ihom.ev F).app G = (closed_counit F).app G := rfl

lemma ihom_coev_app (F G : D ⥤ C) :
  (ihom.coev F).app G = (closed_unit F).app G := rfl

end category_theory.functor
