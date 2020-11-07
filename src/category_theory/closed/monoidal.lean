/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.adjunction.basic
import category_theory.adjunction.opposites

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/
universes v u u₂

namespace category_theory
namespace monoidal

open category monoidal_category

variables {C : Type u} [category.{v} C] [monoidal_category.{v} C]

/-- An object `X` is (left) closed if `(X ⊗ -)` is a left adjoint. -/
class closed (X : C) :=
(is_adj : is_left_adjoint (tensor_left X))

/-- A monoidal category `C` is (left) monoidal closed if every object is (left) closed. -/
class monoidal_closed (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
(closed : Π (X : C), closed X)

attribute [instance, priority 100] monoidal_closed.closed

/--
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unit_closed : closed (𝟙_ C) :=
{ is_adj :=
  begin
    apply adjunction.left_adjoint_of_nat_iso (left_unitor_nat_iso _).symm,
    exact functor.left_adjoint_of_equivalence,
  end }

/--
If `X` and `Y` are exponentiable then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def tensor_closed {X Y : C}
  (hX : closed X) (hY : closed Y) : closed (X ⊗ Y) :=
{ is_adj :=
  begin
    haveI := hX.is_adj,
    haveI := hY.is_adj,
    exact adjunction.left_adjoint_of_nat_iso (monoidal_category.tensor_left_tensor _ _).symm
  end }

variables (A : C) [closed A]

/-- This is the functor `X ↦ (A ⟹ X)`, sometimes written `X ↦ [A, X]`. -/
def internal_hom_right : C ⥤ C := (@closed.is_adj _ _ _ A _).right

notation A ` ⟹ `:20 B:20 := (monoidal.internal_hom_right A).obj B

/-- The adjunction between A ⨯ - and (A ⟹ -). -/
def internal_hom.adjunction : tensor_left A ⊣ internal_hom_right A := closed.is_adj.adj

/-- The evaluation natural transformation. -/
def ev : internal_hom_right A ⋙ tensor_left A ⟶ 𝟭 C :=
closed.is_adj.adj.counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensor_left A ⋙ internal_hom_right A :=
closed.is_adj.adj.unit

@[simp, reassoc]
def ev_naturality {X Y : C} (f : X ⟶ Y) :
  (𝟙 A ⊗ (internal_hom_right A).map f) ≫ (ev A).app Y = (ev A).app X ≫ f :=
(ev A).naturality f

@[simp, reassoc]
lemma coev_naturality {X Y : C} (f : X ⟶ Y) :
  f ≫ (coev A).app Y = (coev A).app X ≫ (internal_hom_right A).map (𝟙 A ⊗ f) :=
(coev A).naturality f

@[simp, reassoc] lemma ev_coev {B : C} :
  (𝟙 A ⊗ ((coev A).app B)) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
adjunction.left_triangle_components (internal_hom.adjunction A)

@[simp, reassoc] lemma coev_ev {B : C} :
  (coev A).app (A⟹B) ≫ (internal_hom_right A).map ((ev A).app B) = 𝟙 (A⟹B) :=
adjunction.right_triangle_components (internal_hom.adjunction A)

variables {A} {X Y : C}

def currying : (A ⊗ Y ⟶ X) ≃ (Y ⟶ A ⟹ X) :=
(internal_hom.adjunction A).hom_equiv Y X

abbreviation curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟹ X) := currying
abbreviation uncurry : (Y ⟶ A ⟹ X) → (A ⊗ Y ⟶ X) := currying.symm

@[simp] lemma adj_hom_equiv_apply_eq (f : A ⊗ Y ⟶ X) :
  (internal_hom.adjunction A).hom_equiv Y X f = curry f :=
rfl
@[simp] lemma adj_hom_equiv_apply_symm_eq (f : Y ⟶ A ⟹ X) :
  ((internal_hom.adjunction A).hom_equiv _ _).symm f = uncurry f :=
rfl

def hom_one_iso_id [closed (𝟙_ C)] : internal_hom_right (𝟙_ C) ≅ 𝟭 C :=
adjunction.nat_iso_of_left_adjoint_nat_iso
  (internal_hom.adjunction (𝟙_ C))
  adjunction.id
  (left_unitor_nat_iso C)

section pre

end pre
#exit


end monoidal
end category_theory
