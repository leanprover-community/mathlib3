/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monoidal.category
import category_theory.adjunction.limits

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/
universes v u u₂

namespace category_theory

open category monoidal_category

/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class closed {C : Type u} [category.{v} C] [monoidal_category.{v} C] (X : C) :=
(is_adj : is_left_adjoint (tensor_left X))

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class monoidal_closed (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
(closed : Π (X : C), closed X)

attribute [instance, priority 100] monoidal_closed.closed

variables {C : Type u} [category.{v} C] [monoidal_category.{v} C]

/--
If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
def tensor_closed {X Y : C}
  (hX : closed X) (hY : closed Y) : closed (X ⊗ Y) :=
{ is_adj :=
  begin
    haveI := hX.is_adj,
    haveI := hY.is_adj,
    exact adjunction.left_adjoint_of_nat_iso (monoidal_category.tensor_left_tensor _ _).symm
  end }

/--
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unit_closed : closed (𝟙_ C) :=
{ is_adj :=
  { right := 𝟭 C,
    adj := adjunction.mk_of_hom_equiv
    { hom_equiv := λ X _,
      { to_fun := λ a, (left_unitor X).inv ≫ a,
        inv_fun := λ a, (left_unitor X).hom ≫ a,
        left_inv := by tidy,
        right_inv := by tidy },
      hom_equiv_naturality_left_symm' := λ X' X Y f g,
      by { dsimp, rw left_unitor_naturality_assoc } } } }

variables (A B : C) {X X' Y Y' Z : C}

variables [closed A]

/-- This is the internal hom `A ⟹ -`. -/
def ihom : C ⥤ C :=
(@closed.is_adj _ _ _ A _).right

namespace ihom

/-- The adjunction between `A ⊗ -` and `A ⟹ -`. -/
def adjunction : tensor_left A ⊣ ihom A :=
closed.is_adj.adj

/-- The evaluation natural transformation. -/
def ev : ihom A ⋙ tensor_left A ⟶ 𝟭 C :=
(ihom.adjunction A).counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensor_left A ⋙ ihom A :=
(ihom.adjunction A).unit

@[simp] lemma ihom_adjunction_counit : (ihom.adjunction A).counit = ev A := rfl
@[simp] lemma ihom_adjunction_unit : (ihom.adjunction A).unit = coev A := rfl

@[simp, reassoc]
lemma ev_naturality {X Y : C} (f : X ⟶ Y) :
  ((𝟙 A) ⊗ ((ihom A).map f)) ≫ (ev A).app Y = (ev A).app X ≫ f :=
(ev A).naturality f

@[simp, reassoc]
lemma coev_naturality {X Y : C} (f : X ⟶ Y) :
  f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map ((𝟙 A) ⊗ f) :=
(coev A).naturality f

notation A ` ⟶[C] `:20 B:19 := (ihom A).obj B

@[simp, reassoc] lemma ev_coev :
  ((𝟙 A) ⊗ ((coev A).app B)) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
adjunction.left_triangle_components (ihom.adjunction A)

@[simp, reassoc] lemma coev_ev :
  (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
adjunction.right_triangle_components (ihom.adjunction A)

end ihom

open category_theory.limits

instance : preserves_colimits (tensor_left A) :=
(ihom.adjunction A).left_adjoint_preserves_colimits

end category_theory
