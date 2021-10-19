/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.opposites

/-!
# The constant functor

`const J : C ⥤ (J ⥤ C)` is the functor that sends an object `X : C` to the functor `J ⥤ C` sending
every object in `J` to `X`, and every morphism to `𝟙 X`.

When `J` is nonempty, `const` is faithful.

We have `(const J).obj X ⋙ F ≅ (const J).obj (F.obj X)` for any `F : C ⥤ D`.
-/

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory

namespace category_theory.functor

variables (J : Type u₁) [category.{v₁} J]
variables {C : Type u₂} [category.{v₂} C]

/--
The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
def const : C ⥤ (J ⥤ C) :=
{ obj := λ X,
  { obj := λ j, X,
    map := λ j j' f, 𝟙 X },
  map := λ X Y f, { app := λ j, f } }

namespace const
open opposite

variables {J}

@[simp] lemma obj_obj (X : C) (j : J) : ((const J).obj X).obj j = X := rfl
@[simp] lemma obj_map (X : C) {j j' : J} (f : j ⟶ j') : ((const J).obj X).map f = 𝟙 X := rfl
@[simp] lemma map_app {X Y : C} (f : X ⟶ Y) (j : J) : ((const J).map f).app j = f := rfl

/--
The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
def op_obj_op (X : C) :
  (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op :=
{ hom := { app := λ j, 𝟙 _ },
  inv := { app := λ j, 𝟙 _ } }

@[simp] lemma op_obj_op_hom_app (X : C) (j : Jᵒᵖ) : (op_obj_op X).hom.app j = 𝟙 _ := rfl
@[simp] lemma op_obj_op_inv_app (X : C) (j : Jᵒᵖ) : (op_obj_op X).inv.app j = 𝟙 _ := rfl

/--
The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def op_obj_unop (X : Cᵒᵖ) :
  (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).left_op :=
{ hom := { app := λ j, 𝟙 _ },
  inv := { app := λ j, 𝟙 _ } }

-- Lean needs some help with universes here.
@[simp] lemma op_obj_unop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (op_obj_unop.{v₁ v₂} X).hom.app j = 𝟙 _ :=
rfl
@[simp] lemma op_obj_unop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (op_obj_unop.{v₁ v₂} X).inv.app j = 𝟙 _ :=
rfl

@[simp] lemma unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
  (unop ((functor.op (const J)).obj X)).map f = 𝟙 (unop X) := rfl
end const



section
variables {D : Type u₃} [category.{v₃} D]

/-- These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps] def const_comp (X : C) (F : C ⥤ D) :
  (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
instance [nonempty J] : faithful (const J : C ⥤ J ⥤ C) :=
{ map_injective' := λ X Y f g e, nat_trans.congr_app e (classical.arbitrary J) }

end

end category_theory.functor
