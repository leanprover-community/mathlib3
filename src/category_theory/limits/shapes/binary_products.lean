/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.discrete_category

/-!
# Binary (co)products

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.
-/

universes v u

open category_theory

namespace category_theory.limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
@[derive decidable_eq]
inductive walking_pair : Type v
| left | right

instance fintype_walking_pair : fintype walking_pair :=
{ elems := [walking_pair.left, walking_pair.right].to_finset,
  complete := λ x, by { cases x; simp } }

def pair_function {C : Type u} (X Y : C) : walking_pair → C
| walking_pair.left := X
| walking_pair.right := Y

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

def pair (X Y : C) : discrete walking_pair ⥤ C :=
functor.of_function (pair_function X Y)

@[simp] lemma pair_obj_left (X Y : C) : (pair X Y).obj walking_pair.left = X := rfl
@[simp] lemma pair_obj_right (X Y : C) : (pair X Y).obj walking_pair.right = Y := rfl

def map_pair {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : pair W X ⟶ pair Y Z :=
{ app := λ j, match j with
  | walking_pair.left := f
  | walking_pair.right := g
  end }

@[simp] lemma map_pair_left {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : (map_pair f g).app walking_pair.left = f := rfl
@[simp] lemma map_pair_right {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : (map_pair f g).app walking_pair.right = g := rfl

abbreviation binary_fan (X Y : C) := cone (pair X Y)
abbreviation binary_cofan (X Y : C) := cocone (pair X Y)

variables {X Y : C}

def binary_fan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : binary_fan X Y :=
{ X := P,
  π := { app := λ j, walking_pair.cases_on j π₁ π₂ }}
def binary_cofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : binary_cofan X Y :=
{ X := P,
  ι := { app := λ j, walking_pair.cases_on j ι₁ ι₂ }}

@[simp] lemma binary_fan.mk_π_app_left {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.left = π₁ := rfl
@[simp] lemma binary_fan.mk_π_app_right {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.right = π₂ := rfl
@[simp] lemma binary_cofan.mk_π_app_left {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.left = ι₁ := rfl
@[simp] lemma binary_cofan.mk_π_app_right {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.right = ι₂ := rfl

abbreviation prod (X Y : C) [has_limit (pair X Y)] := limit (pair X Y)
abbreviation coprod (X Y : C) [has_colimit (pair X Y)] := colimit (pair X Y)

notation X ` ×' `:20 Y:20 := prod X Y
notation X ` ⊕' `:20 Y:20 := coprod X Y

abbreviation prod.fst {X Y : C} [has_limit (pair X Y)] : X ×' Y ⟶ X :=
limit.π (pair X Y) walking_pair.left
abbreviation prod.snd {X Y : C} [has_limit (pair X Y)] : X ×' Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right
abbreviation coprod.inl {X Y : C} [has_colimit (pair X Y)] : X ⟶ X ⊕' Y :=
colimit.ι (pair X Y) walking_pair.left
abbreviation coprod.inr {X Y : C} [has_colimit (pair X Y)] : Y ⟶ X ⊕' Y :=
colimit.ι (pair X Y) walking_pair.right

abbreviation prod.lift {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ×' Y :=
limit.lift _ (binary_fan.mk f g)
abbreviation coprod.desc {W X Y : C} [has_colimit (pair X Y)] (f : X ⟶ W) (g : Y ⟶ W) : X ⊕' Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

abbreviation prod.map {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ×' X ⟶ Y ×' Z :=
lim.map (map_pair f g)
abbreviation coprod.map {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊕' X ⟶ Y ⊕' Z :=
colim.map (map_pair f g)

variables (C)

class has_binary_products :=
(has_limits_of_shape : has_limits_of_shape.{v} (discrete walking_pair) C)
class has_binary_coproducts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} (discrete walking_pair) C)

attribute [instance] has_binary_products.has_limits_of_shape has_binary_coproducts.has_colimits_of_shape

instance [has_finite_products.{v} C] : has_binary_products.{v} C :=
{ has_limits_of_shape := by apply_instance }
instance [has_finite_coproducts.{v} C] : has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := by apply_instance }

variables {C}

section

variables {C} [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

-- TODO The `@[simp] def`s below should probably instead have appropriate simp lemmas written.

/-- The braiding isomorphism which swaps a binary product. -/
@[simp] def prod.braiding (P Q : C) : P ×' Q ≅ Q ×' P :=
{ hom := prod.lift prod.snd prod.fst,
  inv := prod.lift prod.snd prod.fst }

/-- The braiding isomorphism is symmetric. -/
@[simp] lemma prod.symmetry (P Q : C) :
  (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
by tidy

/-- The associator isomorphism for binary products. -/
@[simp] def prod.associator
  (P Q R : C) : (P ×' Q) ×' R ≅ P ×' (Q ×' R) :=
{ hom :=
  prod.lift
    (prod.fst ≫ prod.fst)
    (prod.lift (prod.fst ≫ prod.snd) prod.snd),
  inv :=
  prod.lift
    (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.snd ≫ prod.snd) }

variables [has_terminal.{v} C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simp] def prod.left_unitor
  (P : C) : ⊤_ C ×' P ≅ P :=
{ hom := prod.snd,
  inv := prod.lift (terminal.from P) (𝟙 _) }

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simp] def prod.right_unitor
  (P : C) : P ×' ⊤_ C ≅ P :=
{ hom := prod.fst,
  inv := prod.lift (𝟙 _) (terminal.from P) }
end

section
variables {C} [has_binary_coproducts.{v} C]

local attribute [tidy] tactic.case_bash

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simp] def coprod.braiding (P Q : C) : P ⊕' Q ≅ Q ⊕' P :=
{ hom := coprod.desc coprod.inr coprod.inl,
  inv := coprod.desc coprod.inr coprod.inl }

/-- The braiding isomorphism is symmetric. -/
@[simp] lemma coprod.symmetry (P Q : C) :
  (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
by tidy

/-- The associator isomorphism for binary coproducts. -/
@[simp] def coprod.associator
  (P Q R : C) : (P ⊕' Q) ⊕' R ≅ P ⊕' (Q ⊕' R) :=
{ hom :=
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr),
  inv :=
  coprod.desc
    (coprod.inl ≫ coprod.inl)
    (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) }

variables [has_initial.{v} C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simp] def coprod.left_unitor
  (P : C) : ⊥_ C ⊕' P ≅ P :=
{ hom := coprod.desc (initial.to P) (𝟙 _),
  inv := coprod.inr }

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simp] def coprod.right_unitor
  (P : C) : P ⊕' ⊥_ C ≅ P :=
{ hom := coprod.desc (𝟙 _) (initial.to P),
  inv := coprod.inl }
end

end category_theory.limits
