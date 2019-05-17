-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Michael Jendrusch, Scott Morrison
import category_theory.monoidal.tensor_product
import category_theory.natural_isomorphism
import tactic -- TODO switch this back to tactic.basic once relevant PRs land.
import tactic.slice

open category_theory
open tactic

universes v u

open category_theory
open category_theory.category
open category_theory.iso
open category_theory.monoidal

namespace category_theory.monoidal
class monoidal_category (C : Sort u) extends category.{v} C :=
-- curried tensor product of objects:
(tensor_obj               : C → C → C)
-- curried tensor product of morphisms:
(tensor_hom               :
  Π {X₁ Y₁ X₂ Y₂ : C}, hom X₁ Y₁ → hom X₂ Y₂ → hom (tensor_obj X₁ X₂) (tensor_obj Y₁ Y₂))
-- tensor product laws:
(tensor_id'               :
  ∀ (X₁ X₂ : C), tensor_hom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj X₁ X₂) . obviously)
(tensor_comp'             :
  ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
  tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = (tensor_hom f₁ f₂) ≫ (tensor_hom g₁ g₂) . obviously)
-- tensor unit:
(tensor_unit              : C)
-- associator:
(associator               :
  Π X Y Z : C, (tensor_obj (tensor_obj X Y) Z) ≅ (tensor_obj X (tensor_obj Y Z)))
(associator_naturality'   :
  assoc_natural tensor_obj @tensor_hom associator . obviously)
-- left unitor:
(left_unitor              : Π X : C, tensor_obj tensor_unit X ≅ X)
(left_unitor_naturality'  :
  left_unitor_natural tensor_obj @tensor_hom tensor_unit left_unitor . obviously)
-- right unitor:
(right_unitor             : Π X : C, tensor_obj X tensor_unit ≅ X)
(right_unitor_naturality' :
  right_unitor_natural tensor_obj @tensor_hom tensor_unit right_unitor . obviously)
-- pentagon identity:
(pentagon'                : pentagon @tensor_hom associator . obviously)
-- triangle identity:
(triangle'                :
  triangle @tensor_hom left_unitor right_unitor associator . obviously)

restate_axiom monoidal_category.tensor_id'
attribute [simp] monoidal_category.tensor_id
restate_axiom monoidal_category.tensor_comp'
attribute [simp] monoidal_category.tensor_comp
restate_axiom monoidal_category.associator_naturality'
restate_axiom monoidal_category.left_unitor_naturality'
restate_axiom monoidal_category.right_unitor_naturality'
restate_axiom monoidal_category.pentagon'
restate_axiom monoidal_category.triangle'
attribute [simp] monoidal_category.triangle

open monoidal_category

infixr ` ⊗ `:70 := tensor_obj
infixr ` ⊗ `:70 := tensor_hom

def tensor_iso {C : Sort u} {X Y X' Y' : C} [monoidal_category.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    X ⊗ X' ≅ Y ⊗ Y' :=
{ hom := f.hom ⊗ g.hom,
  inv := f.inv ⊗ g.inv,
  hom_inv_id' := by rw [←tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ←tensor_id],
  inv_hom_id' := by rw [←tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ←tensor_id] }

infixr ` ⊗ `:70 := tensor_iso

section

variables {C : Sort u} [𝒞 : monoidal_category.{v} C]
include 𝒞

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : is_iso (f ⊗ g) :=
{ ..(as_iso f ⊗ as_iso g) }

@[simp] lemma inv_tensor {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g := rfl

variables {U V W X Y Z : C}

-- When `rewrite_search` lands, add @[search] attributes to

-- monoidal_category.tensor_id monoidal_category.tensor_comp monoidal_category.associator_naturality
-- monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality
-- monoidal_category.pentagon monoidal_category.triangle

-- interchange interchange_left_identity interchange_right_identity interchange_identities
-- triangle_1 triangle_2 triangle_3 triangle_4
-- left_unitor_product left_unitor_product_inv
-- right_unitor_product right_unitor_product_inv
-- pentagon_inv
-- associator_inv_naturality
-- left_unitor_inv_naturality
-- right_unitor_inv_naturality

@[simp] lemma tensor_comp_id (f : W ⟶ X) (g : X ⟶ Y) :
  (f ≫ g) ⊗ (𝟙 Z) = (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) :=
by { rw ←tensor_comp, simp }

@[simp] lemma tensor_id_comp (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z) ⊗ (f ≫ g) = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
by { rw ←tensor_comp, simp }

lemma comp_id_tensor_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) :=
by { rw [←tensor_comp, ←tensor_comp], simp }

lemma left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (left_unitor X').inv = (left_unitor X).inv ≫ (𝟙 _ ⊗ f) :=
begin
  apply (cancel_mono (left_unitor X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  conv_rhs { congr, skip, rw [left_unitor_naturality] },
  conv_rhs { rw [←category.assoc], congr, rw [iso.inv_hom_id] },
  conv_rhs { rw [category.id_comp] }
end

lemma right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (right_unitor X').inv = (right_unitor X).inv ≫ (f ⊗ 𝟙 _) :=
begin
  apply (cancel_mono (right_unitor X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  conv_rhs { congr, skip, rw [right_unitor_naturality] },
  conv_rhs { rw [←category.assoc], congr, rw [iso.inv_hom_id] },
  conv_rhs { rw [category.id_comp] }
end

@[simp] lemma tensor_left_iff
  {X Y : C} (f g : X ⟶ Y) :
  ((𝟙 (tensor_unit C)) ⊗ f = (𝟙 (tensor_unit C)) ⊗ g) ↔ (f = g) :=
begin
  split,
  { intro h,
    have h' := congr_arg (λ k, (left_unitor _).inv ≫ k) h,
    dsimp at h',
    rw ←left_unitor_inv_naturality at h',
    rw ←left_unitor_inv_naturality at h',
    exact (cancel_mono _).1 h', },
  { intro h, subst h, }
end

@[simp] lemma tensor_right_iff
  {X Y : C} (f g : X ⟶ Y) :
  (f ⊗ (𝟙 (tensor_unit C)) = g ⊗ (𝟙 (tensor_unit C))) ↔ (f = g) :=
begin
  split,
  { intro h,
    have h' := congr_arg (λ k, (right_unitor _).inv ≫ k) h,
    dsimp at h',
    rw ←right_unitor_inv_naturality at h',
    rw ←right_unitor_inv_naturality at h',
    exact (cancel_mono _).1 h' },
  { intro h, subst h, }
end

-- We now prove:
--   ((associator (tensor_unit C) X Y).hom) ≫
--     ((left_unitor (X ⊗ Y)).hom)
--   = ((left_unitor X).hom ⊗ (𝟙 Y))
-- (and the corresponding fact for right unitors)
-- following the proof on nLab.

lemma left_unitor_product_aux_perimeter (X Y : C) :
    ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom ≫
    ((𝟙 (tensor_unit C)) ⊗ (associator (tensor_unit C) X Y).hom) ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor (X ⊗ Y)).hom)
  = (((right_unitor (tensor_unit C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) X Y).hom :=
begin
  conv_lhs { congr, skip, rw [←category.assoc] },
  conv_lhs { rw [←category.assoc], congr, rw [monoidal_category.pentagon] },
  conv_rhs { rw [associator_naturality], congr, skip, congr, skip, rw [tensor_id] },
  conv_rhs { congr, skip, rw [←monoidal_category.triangle] },
  conv_rhs { rw [←category.assoc] }
end

lemma left_unitor_product_aux_triangle (X Y : C) :
    ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y)) ≫
    (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y))
  = ((right_unitor (tensor_unit C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y) :=
begin
  conv_lhs { rw [←tensor_comp_id] },
  conv_rhs { congr, rw [←monoidal_category.triangle] }
end

lemma left_unitor_product_aux_square (X Y : C) :
    (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom ⊗ (𝟙 Y))
  = (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) X Y).hom :=
begin
  conv_rhs { rw [associator_naturality] }
end

lemma left_unitor_product_aux (X Y : C) :
    ((𝟙 (tensor_unit C)) ⊗ (associator (tensor_unit C) X Y).hom) ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor (X ⊗ Y)).hom)
  = (𝟙 (tensor_unit C)) ⊗ ((left_unitor X).hom ⊗ (𝟙 Y)) :=
begin
  rw ←(cancel_epi (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom),
  rw left_unitor_product_aux_square,
  rw ←(cancel_epi ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y))),
  slice_rhs 1 2 { rw left_unitor_product_aux_triangle },
  conv_lhs { rw [left_unitor_product_aux_perimeter] }
end

lemma right_unitor_product_aux_perimeter (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom :=
begin
  transitivity (((associator X Y _).hom ⊗ 𝟙 _) ≫ (associator X _ _).hom ≫
    (𝟙 X ⊗ (associator Y _ _).hom)) ≫
    (𝟙 X ⊗ 𝟙 Y ⊗ (monoidal_category.left_unitor _).hom),
  { conv_lhs { congr, skip, rw [←category.assoc] },
    conv_rhs { rw [category.assoc] } },
  { conv_lhs { congr, rw [monoidal_category.pentagon] },
    conv_rhs { congr, rw [←monoidal_category.triangle] },
    conv_rhs { rw [category.assoc] },
    conv_rhs { congr, skip, congr, congr, rw [←tensor_id] },
    conv_rhs { congr, skip, rw [associator_naturality] },
    conv_rhs { rw [←category.assoc] } }
end

lemma right_unitor_product_aux_triangle (X Y : C) :
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = (𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)) :=
begin
  conv_lhs { rw [←tensor_id_comp] },
  conv_rhs { congr, skip, rw [←monoidal_category.triangle] }
end

lemma right_unitor_product_aux_square (X Y : C) :
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)))
  = (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom :=
begin
  conv_rhs { rw [associator_naturality] }
end

lemma right_unitor_product_aux (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C)))
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) :=
begin
  rw ←(cancel_mono (associator X Y (tensor_unit C)).hom),
  slice_lhs 2 3 { rw ←right_unitor_product_aux_square },
  conv_lhs { congr, skip, congr, skip, rw [←right_unitor_product_aux_triangle] },
  conv_rhs { rw [←right_unitor_product_aux_perimeter] }
end

-- See Proposition 2.2.4 of http://www-math.mit.edu/~etingof/egnobookfinal.pdf
@[simp] lemma left_unitor_product (X Y : C) :
  ((associator (tensor_unit C) X Y).hom) ≫ ((left_unitor (X ⊗ Y)).hom) =
    ((left_unitor X).hom ⊗ (𝟙 Y)) :=
by rw [←tensor_left_iff, tensor_id_comp, left_unitor_product_aux]

@[simp] lemma left_unitor_product_inv (X Y : C) :
  ((left_unitor (X ⊗ Y)).inv) ≫ ((associator (tensor_unit C) X Y).inv) =
    ((left_unitor X).inv ⊗ (𝟙 Y)) :=
eq_of_inv_eq_inv (by simp)

@[simp] lemma right_unitor_product (X Y : C) :
  ((associator X Y (tensor_unit C)).hom) ≫ ((𝟙 X) ⊗ (right_unitor Y).hom) =
    ((right_unitor (X ⊗ Y)).hom) :=
by rw [←tensor_right_iff, tensor_comp_id, right_unitor_product_aux]

@[simp] lemma right_unitor_product_inv (X Y : C) :
  ((𝟙 X) ⊗ (right_unitor Y).inv) ≫ ((associator X Y (tensor_unit C)).inv) =
    ((right_unitor (X ⊗ Y)).inv) :=
eq_of_inv_eq_inv (by simp)

lemma associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
  (f ⊗ (g ⊗ h)) ≫ (associator X' Y' Z').inv = (associator X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
begin
  apply (cancel_mono (associator X' Y' Z').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  conv_rhs { congr, skip, rw [associator_naturality] },
  conv_rhs { rw [←category.assoc], congr, rw [iso.inv_hom_id] },
  conv_rhs { rw [category.id_comp] }
end

lemma pentagon_inv (W X Y Z : C) :
  ((𝟙 W) ⊗ (associator X Y Z).inv) ≫ (associator W (X ⊗ Y) Z).inv ≫ ((associator W X Y).inv ⊗ (𝟙 Z))
    = (associator W X (Y ⊗ Z)).inv ≫ (associator (W ⊗ X) Y Z).inv :=
begin
  apply category_theory.eq_of_inv_eq_inv,
  dsimp,
  rw [category.assoc, monoidal_category.pentagon]
end

@[simp] lemma triangle_1 (X Y : C) :
  (associator X (tensor_unit C) Y).hom ≫ ((𝟙 X) ⊗ (left_unitor Y).hom) = (right_unitor X).hom ⊗ 𝟙 Y :=
monoidal_category.triangle C X Y

@[simp] lemma triangle_2 (X Y : C) :
  (associator X (tensor_unit C) Y).inv ≫ ((right_unitor X).hom ⊗ 𝟙 Y) = ((𝟙 X) ⊗ (left_unitor Y).hom) :=
begin
  conv_lhs { congr, skip, rw [←triangle_1] },
  conv_lhs { rw [←category.assoc], congr, rw [iso.inv_hom_id] },
  conv_lhs { rw [category.id_comp] }
end

@[simp] lemma triangle_3 (X Y : C) :
  ((right_unitor X).inv ⊗ 𝟙 Y) ≫ (associator X (tensor_unit C) Y).hom = ((𝟙 X) ⊗ (left_unitor Y).inv) :=
begin
  apply (cancel_mono (𝟙 X ⊗ (left_unitor Y).hom)).1,
  simp only [assoc, triangle_1],
  conv_lhs { rw [←tensor_comp_id, iso.inv_hom_id] },
  conv_rhs { rw [←tensor_id_comp, iso.inv_hom_id] }
end

@[simp] lemma triangle_4 (X Y : C) :
  ((𝟙 X) ⊗ (left_unitor Y).inv) ≫ (associator X (tensor_unit C) Y).inv = ((right_unitor X).inv ⊗ 𝟙 Y) :=
begin
  apply (cancel_mono ((right_unitor X).hom ⊗ 𝟙 Y)).1,
  simp only [triangle_2, assoc],
  conv_lhs { rw [←tensor_id_comp, iso.inv_hom_id] },
  conv_rhs { rw [←tensor_comp_id, iso.inv_hom_id] }
end

end

namespace monoidal_category

-- In order to be able to describe the tensor product as a functor, we
-- need to be up in at least `Type 0` for both objects and morphisms,
-- so that we can construct products.
variables (C : Type u) [𝒞 : monoidal_category.{v+1} C]
include 𝒞

def tensor : (C × C) ⥤ C :=
{ obj := λ X, tensor_obj X.1 X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), tensor_hom f.1 f.2 }

def left_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, (X.1 ⊗ X.2.1) ⊗ X.2.2,
  map := λ {X Y : C × C × C} (f : X ⟶ Y), (f.1 ⊗ f.2.1) ⊗ f.2.2 }

@[simp] lemma left_assoc_tensor_obj (X) :
  (left_assoc_tensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 := rfl
@[simp] lemma left_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (left_assoc_tensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 := rfl

def right_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ (X.2.1 ⊗ X.2.2),
  map := λ {X Y : C × C × C} (f : X ⟶ Y), f.1 ⊗ (f.2.1 ⊗ f.2.2) }

@[simp] lemma right_assoc_tensor_obj (X) :
  (right_assoc_tensor C).obj X = X.1 ⊗ (X.2.1 ⊗ X.2.2) := rfl
@[simp] lemma right_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (right_assoc_tensor C).map f = f.1 ⊗ (f.2.1 ⊗ f.2.2) := rfl

def tensor_unit_left : C ⥤ C :=
{ obj := λ X, tensor_unit C ⊗ X,
  map := λ {X Y : C} (f : X ⟶ Y), (𝟙 (tensor_unit C)) ⊗ f }
def tensor_unit_right : C ⥤ C :=
{ obj := λ X, X ⊗ tensor_unit C,
  map := λ {X Y : C} (f : X ⟶ Y), f ⊗ (𝟙 (tensor_unit C)) }

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.

def associator_nat_iso :
  left_assoc_tensor C ≅ right_assoc_tensor C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.associator)
  (by intros; dsimp; apply monoidal_category.associator_naturality)

def left_unitor_nat_iso :
  tensor_unit_left C ≅ functor.id C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.left_unitor)
  (by intros; dsimp; apply monoidal_category.left_unitor_naturality)

def right_unitor_nat_iso :
  tensor_unit_right C ≅ functor.id C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.right_unitor)
  (by intros; dsimp; apply monoidal_category.right_unitor_naturality)

end monoidal_category

end category_theory.monoidal
