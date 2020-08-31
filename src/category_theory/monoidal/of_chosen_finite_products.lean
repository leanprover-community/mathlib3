/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.braided
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal
import category_theory.pempty

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## Implementation
For the sake of nicer definitional properties,
we rely on `has_terminal` and `has_binary_products` instead of `has_finite_products`,
so that if a particular category provides customised instances of these
we pick those up instead.
-/

universes v u

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {X Y : C}

namespace limits

section
variables {C}

def binary_fan.swap {P Q : C} (t : binary_fan P Q) : binary_fan Q P :=
binary_fan.mk t.snd t.fst

@[simp] lemma binary_fan.swap_fst {P Q : C} (t : binary_fan P Q) : t.swap.fst = t.snd := rfl
@[simp] lemma binary_fan.swap_snd {P Q : C} (t : binary_fan P Q) : t.swap.snd = t.fst := rfl

/--
If a cone `t` over `P Q` is a limit cone, then `t.swap` is a limit cone over `Q P`.
-/
@[simps]
def is_limit.swap_binary_fan {P Q : C} {t : binary_fan P Q} (I : is_limit t) : is_limit t.swap :=
{ lift := λ s, I.lift (binary_fan.swap s),
  fac' := λ s, by { rintro ⟨⟩; simp, },
  uniq' := λ s m w,
  begin
    have h := I.uniq (binary_fan.swap s) m,
    rw h,
    intro j,
    specialize w j.swap,
    cases j; exact w,
  end }

/--
Construct `has_binary_product Q P` from `has_binary_product P Q`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
def has_binary_product.swap (P Q : C) [has_binary_product P Q] : has_binary_product Q P :=
has_limit.mk ⟨binary_fan.swap (limit.cone (pair P Q)), (limit.is_limit (pair P Q)).swap_binary_fan⟩

def prod.braiding {X Y : C} {s : binary_fan X Y} (P : is_limit s) {t : binary_fan Y X} (Q : is_limit t) :
  s.X ≅ t.X :=
is_limit.cone_point_unique_up_to_iso P Q.swap_binary_fan

def binary_fan.assoc {X Y Z : C} {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  binary_fan X sYZ.X :=
binary_fan.mk (s.fst ≫ sXY.fst) (Q.lift (binary_fan.mk (s.fst ≫ sXY.snd) s.snd))

@[simp] lemma binary_fan.assoc_fst {X Y Z : C} {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  (s.assoc Q).fst = s.fst ≫ sXY.fst := rfl
@[simp] lemma binary_fan.assoc_snd {X Y Z : C} {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  (s.assoc Q).snd = Q.lift (binary_fan.mk (s.fst ≫ sXY.snd) s.snd) := rfl

def binary_fan.assoc_inv {X Y Z : C} {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  binary_fan sXY.X Z :=
binary_fan.mk (P.lift (binary_fan.mk s.fst (s.snd ≫ sYZ.fst))) (s.snd ≫ sYZ.snd)

@[simp] lemma binary_fan.assoc_inv_fst {X Y Z : C} {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  (s.assoc_inv P).fst = P.lift (binary_fan.mk s.fst (s.snd ≫ sYZ.fst)) := rfl
@[simp] lemma binary_fan.assoc_inv_snd {X Y Z : C} {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  (s.assoc_inv P).snd = s.snd ≫ sYZ.snd := rfl

@[simps]
def is_limit.assoc {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
  {s : binary_fan sXY.X Z} (R : is_limit s) : is_limit (s.assoc Q) :=
{ lift := λ t, R.lift (binary_fan.assoc_inv P t),
  fac' := λ t,
  begin
    rintro ⟨⟩; simp,
    apply Q.hom_ext,
    rintro ⟨⟩; simp,
  end,
  uniq' := λ t m w,
  begin
    have h := R.uniq (binary_fan.assoc_inv P t) m,
    rw h,
    rintro ⟨⟩; simp,
    apply P.hom_ext,
    rintro ⟨⟩; simp,
    { exact w walking_pair.left, },
    { specialize w walking_pair.right,
      simp at w,
      rw [←w], simp, },
    { specialize w walking_pair.right,
      simp at w,
      rw [←w], simp, },
  end, }

def prod.assoc {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
  {s : binary_fan sXY.X Z} (R : is_limit s) {t : binary_fan X sYZ.X} (S : is_limit t) :
  s.X ≅ t.X :=
is_limit.cone_point_unique_up_to_iso (is_limit.assoc P Q R) S

def prod.assoc_of_limit_data
  (L : Π X Y : C, limit_data (pair X Y)) (X Y Z : C) :
  (L (L X Y).cone.X Z).cone.X ≅ (L X (L Y Z).cone.X).cone.X :=
prod.assoc (L X Y).is_limit (L Y Z).is_limit (L (L X Y).cone.X Z).is_limit (L X (L Y Z).cone.X).is_limit

@[simps]
def prod.left_unitor
  {X : C} {s : cone (functor.empty C)} (P : is_limit s) {t : binary_fan s.X X} (Q : is_limit t) :
  t.X ≅ X :=
{ hom := t.snd,
  inv := Q.lift (binary_fan.mk (P.lift { X := X, π := { app := pempty.rec _ } }) (𝟙 X) ),
  hom_inv_id' := by { apply Q.hom_ext, rintro ⟨⟩, { apply P.hom_ext, rintro ⟨⟩, }, { simp, }, }, }

@[simps]
def prod.right_unitor
  {X : C} {s : cone (functor.empty C)} (P : is_limit s) {t : binary_fan X s.X} (Q : is_limit t) :
  t.X ≅ X :=
{ hom := t.fst,
  inv := Q.lift (binary_fan.mk (𝟙 X) (P.lift { X := X, π := { app := pempty.rec _ } })),
  hom_inv_id' := by { apply Q.hom_ext, rintro ⟨⟩, { simp, }, { apply P.hom_ext, rintro ⟨⟩, }, }, }

end

end limits

open category_theory.limits

section
local attribute [tidy] tactic.case_bash

variables {C}
variables (𝒯 : limit_data (functor.empty C))
variables (ℬ : Π (X Y : C), limit_data (pair X Y))

def tensor_obj (X Y : C) : C := (ℬ X Y).cone.X
def tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : tensor_obj ℬ W Y ⟶ tensor_obj ℬ X Z :=
  (binary_fan.is_limit.lift' (ℬ X Z).is_limit
    ((ℬ W Y).cone.π.app walking_pair.left ≫ f)
    (((ℬ W Y).cone.π.app walking_pair.right : (ℬ W Y).cone.X ⟶ Y) ≫ g)).val

lemma tensor_id (X₁ X₂ : C) : tensor_hom ℬ (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj ℬ X₁ X₂) :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩;
  { dsimp, simp, erw [category.id_comp], },
end

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  tensor_hom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) =
    tensor_hom ℬ f₁ f₂ ≫ tensor_hom ℬ g₁ g₂ :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩;
  { dsimp, simp, },
end

lemma pentagon (W X Y Z : C) :
  tensor_hom ℬ (prod.assoc_of_limit_data ℬ W X Y).hom (𝟙 Z) ≫
    (prod.assoc_of_limit_data ℬ W (tensor_obj ℬ X Y) Z).hom ≫
      tensor_hom ℬ (𝟙 W) (prod.assoc_of_limit_data ℬ X Y Z).hom =
  (prod.assoc_of_limit_data ℬ (tensor_obj ℬ W X) Y Z).hom ≫
    (prod.assoc_of_limit_data ℬ W X (tensor_obj ℬ Y Z)).hom :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
  { simp, },
  { apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    { simp, }, }
end

lemma triangle (X Y : C) :
  (prod.assoc_of_limit_data ℬ X 𝒯.cone.X Y).hom ≫
    tensor_hom ℬ (𝟙 X) (prod.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X Y).is_limit).hom =
  tensor_hom ℬ (prod.right_unitor 𝒯.is_limit (ℬ X 𝒯.cone.X).is_limit).hom (𝟙 Y) :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩; simp,
end

lemma left_unitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
  tensor_hom ℬ (𝟙 𝒯.cone.X) f ≫ (prod.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X X₂).is_limit).hom =
    (prod.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X X₁).is_limit).hom ≫ f :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  simp,
end

lemma right_unitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
  tensor_hom ℬ f (𝟙 𝒯.cone.X) ≫ (prod.right_unitor 𝒯.is_limit (ℬ X₂ 𝒯.cone.X).is_limit).hom =
    (prod.right_unitor 𝒯.is_limit (ℬ X₁ 𝒯.cone.X).is_limit).hom ≫ f :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  simp,
end

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  tensor_hom ℬ (tensor_hom ℬ f₁ f₂) f₃ ≫ (prod.assoc_of_limit_data ℬ Y₁ Y₂ Y₃).hom =
    (prod.assoc_of_limit_data ℬ X₁ X₂ X₃).hom ≫ tensor_hom ℬ f₁ (tensor_hom ℬ f₂ f₃) :=
begin
  dsimp [prod.assoc_of_limit_data, prod.assoc, tensor_hom, tensor_obj],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
  { simp, },
  { apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    { simp, }, },
end

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_chosen_finite_products :
  monoidal_category C :=
{ tensor_unit  := 𝒯.cone.X,
  tensor_obj   := λ X Y, tensor_obj ℬ X Y,
  tensor_hom   := λ _ _ _ _ f g, tensor_hom ℬ f g,
  tensor_id'   := tensor_id ℬ,
  tensor_comp' := λ _ _ _ _ _ _ f₁ f₂ g₁ g₂, tensor_comp ℬ f₁ f₂ g₁ g₂,
  associator   := λ X Y Z, prod.assoc_of_limit_data ℬ X Y Z,
  left_unitor  := λ X, prod.left_unitor (𝒯.is_limit) (ℬ 𝒯.cone.X X).is_limit,
  right_unitor := λ X, prod.right_unitor (𝒯.is_limit) (ℬ X 𝒯.cone.X).is_limit,
  pentagon'    := pentagon ℬ,
  triangle'    := triangle 𝒯 ℬ,
  left_unitor_naturality' := λ _ _ f, left_unitor_naturality 𝒯 ℬ f,
  right_unitor_naturality' := λ _ _ f, right_unitor_naturality 𝒯 ℬ f,
  associator_naturality' := λ _ _ _ _ _ _ f₁ f₂ f₃, associator_naturality ℬ f₁ f₂ f₃, }

open monoidal_category

@[derive category]
def monoidal_of_chosen_finite_products_synonym
  (𝒯 : limit_data (functor.empty C)) (ℬ : Π (X Y : C), limit_data (pair X Y)):= C

instance : monoidal_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
monoidal_of_chosen_finite_products 𝒯 ℬ

lemma braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
  (tensor_hom ℬ f g) ≫ (limits.prod.braiding (ℬ Y Y').is_limit (ℬ Y' Y).is_limit).hom =
    (limits.prod.braiding (ℬ X X').is_limit (ℬ X' X).is_limit).hom ≫ (tensor_hom ℬ g f) :=
begin
  dsimp [tensor_hom, limits.prod.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

lemma hexagon_forward (X Y Z : C) :
  (prod.assoc_of_limit_data ℬ X Y Z).hom ≫
    (limits.prod.braiding (ℬ X (tensor_obj ℬ Y Z)).is_limit (ℬ (tensor_obj ℬ Y Z) X).is_limit).hom ≫
        (prod.assoc_of_limit_data ℬ Y Z X).hom =
    (tensor_hom ℬ (limits.prod.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom (𝟙 Z)) ≫
      (prod.assoc_of_limit_data ℬ Y X Z).hom ≫
        (tensor_hom ℬ (𝟙 Y) (limits.prod.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom) :=
begin
  dsimp [tensor_obj, tensor_hom, limits.prod.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩,
  { dsimp [prod.assoc_of_limit_data, prod.assoc, limits.is_limit.cone_point_unique_up_to_iso], simp, },
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
    { dsimp [prod.assoc_of_limit_data, prod.assoc, limits.is_limit.cone_point_unique_up_to_iso], simp, }, }
end

lemma hexagon_reverse (X Y Z : C) :
  (prod.assoc_of_limit_data ℬ X Y Z).inv ≫
    (limits.prod.braiding (ℬ (tensor_obj ℬ X Y) Z).is_limit (ℬ Z (tensor_obj ℬ X Y)).is_limit).hom ≫
      (prod.assoc_of_limit_data ℬ Z X Y).inv =
    (tensor_hom ℬ (𝟙 X) (limits.prod.braiding (ℬ Y Z).is_limit (ℬ Z Y).is_limit).hom) ≫
      (prod.assoc_of_limit_data ℬ X Z Y).inv ≫
        (tensor_hom ℬ (limits.prod.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom (𝟙 Y)) :=
begin
  dsimp [tensor_obj, tensor_hom, limits.prod.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩,
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
    { dsimp [prod.assoc_of_limit_data, prod.assoc, limits.is_limit.cone_point_unique_up_to_iso], simp, }, },
  { dsimp [prod.assoc_of_limit_data, prod.assoc, limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

lemma symmetry (X Y : C) :
  (limits.prod.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom ≫
      (limits.prod.braiding (ℬ Y X).is_limit (ℬ X Y).is_limit).hom =
    𝟙 (tensor_obj ℬ X Y) :=
begin
  dsimp [tensor_obj, tensor_hom, limits.prod.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

/--
The monoidal structure coming from finite products is symmetric.
-/
def symmetric_of_chosen_finite_products :
  symmetric_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
{ braiding := λ X Y, limits.prod.braiding (ℬ _ _).is_limit (ℬ _ _).is_limit,
  braiding_naturality' := λ X X' Y Y' f g, braiding_naturality ℬ f g,
  hexagon_forward' := λ X Y Z, hexagon_forward ℬ X Y Z,
  hexagon_reverse' := λ X Y Z, hexagon_reverse ℬ X Y Z,
  symmetry' := λ X Y, symmetry ℬ X Y, }

end

end category_theory
