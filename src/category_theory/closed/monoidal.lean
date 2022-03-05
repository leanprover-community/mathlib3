/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monoidal.category
import category_theory.adjunction.limits
import category_theory.adjunction.mates

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
(closed' : Π (X : C), closed X)

attribute [instance, priority 100] monoidal_closed.closed'

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

/--
This is the internal hom `A ⟶[C] -`.
Note that this is essentially an opaque definition,
and so will not agree definitionally with any "native" internal hom the category has.

TODO: we could introduce a `has_ihom` class
that allows specifying a particular definition of the internal hom,
and provide a low priority opaque instance.
-/
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

variables {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace monoidal_closed

/-- Currying in a monoidal closed category. -/
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X) :=
(ihom.adjunction A).hom_equiv _ _
/-- Uncurrying in a monoidal closed category. -/
def uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X) :=
((ihom.adjunction A).hom_equiv _ _).symm

@[simp] lemma hom_equiv_apply_eq (f : A ⊗ Y ⟶ X) :
  (ihom.adjunction A).hom_equiv _ _ f = curry f := rfl
@[simp] lemma hom_equiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
  ((ihom.adjunction A).hom_equiv _ _).symm f = uncurry f := rfl

@[reassoc]
lemma curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) :
  curry (((𝟙 _) ⊗ f) ≫ g) = f ≫ curry g :=
adjunction.hom_equiv_naturality_left _ _ _

@[reassoc]
lemma curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
  curry (f ≫ g) = curry f ≫ (ihom _).map g :=
adjunction.hom_equiv_naturality_right _ _ _

@[reassoc]
lemma uncurry_natural_right  (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
  uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
adjunction.hom_equiv_naturality_right_symm _ _ _

@[reassoc]
lemma uncurry_natural_left  (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
  uncurry (f ≫ g) = ((𝟙 _) ⊗ f) ≫ uncurry g :=
adjunction.hom_equiv_naturality_left_symm _ _ _

@[simp]
lemma uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
(closed.is_adj.adj.hom_equiv _ _).left_inv f

@[simp]
lemma curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
(closed.is_adj.adj.hom_equiv _ _).right_inv f

lemma curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) :
  curry f = g ↔ f = uncurry g :=
adjunction.hom_equiv_apply_eq _ f g

lemma eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) :
  g = curry f ↔ uncurry g = f :=
adjunction.eq_hom_equiv_apply _ f g

-- I don't think these two should be simp.
lemma uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = ((𝟙 A) ⊗ g) ≫ (ihom.ev A).app X :=
adjunction.hom_equiv_counit _

lemma curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
adjunction.hom_equiv_unit _

lemma curry_injective : function.injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
(closed.is_adj.adj.hom_equiv _ _).injective

lemma uncurry_injective : function.injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
(closed.is_adj.adj.hom_equiv _ _).symm.injective

variables (A X)

lemma uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X :=
by rw [uncurry_eq, tensor_id, id_comp]

lemma curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X :=
by { rw [curry_eq, (ihom A).map_id (A ⊗ _)], apply comp_id }

section pre

variables {A B} [closed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
transfer_nat_trans_self (ihom.adjunction _) (ihom.adjunction _) ((tensoring_left C).map f)

lemma id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
  (𝟙 B ⊗ ((pre f).app X)) ≫ (ihom.ev B).app X =
    (f ⊗ (𝟙 (A ⟶[C] X))) ≫ (ihom.ev A).app X :=
transfer_nat_trans_self_counit _ _ ((tensoring_left C).map f) X

lemma uncurry_pre (f : B ⟶ A) (X : C) :
  monoidal_closed.uncurry ((pre f).app X) = (f ⊗ 𝟙 _) ≫ (ihom.ev A).app X :=
by rw [uncurry_eq, id_tensor_pre_app_comp_ev]

lemma coev_app_comp_pre_app (f : B ⟶ A) :
  (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) =
    (ihom.coev B).app X ≫ (ihom B).map (f ⊗ (𝟙 _)) :=
unit_transfer_nat_trans_self _ _ ((tensoring_left C).map f) X

@[simp]
lemma pre_id (A : C) [closed A] : pre (𝟙 A) = 𝟙 _ :=
by { simp only [pre, functor.map_id], dsimp, simp, }

@[simp]
lemma pre_map {A₁ A₂ A₃ : C} [closed A₁] [closed A₂] [closed A₃]
  (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
  pre (f ≫ g) = pre g ≫ pre f :=
by rw [pre, pre, pre, transfer_nat_trans_self_comp, (tensoring_left C).map_comp]

end pre

/-- The internal hom functor given by the monoidal closed structure. -/
def internal_hom [monoidal_closed C] : Cᵒᵖ ⥤ C ⥤ C :=
{ obj := λ X, ihom X.unop,
  map := λ X Y f, pre f.unop }

end monoidal_closed

end category_theory
