/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.products.basic

open category_theory

universes v u

open category_theory
open category_theory.category
open category_theory.iso

namespace category_theory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.
-/
class monoidal_category (C : Type u) [𝒞 : category.{v} C] :=
-- curried tensor product of objects:
(tensor_obj               : C → C → C)
(infixr ` ⊗ `:70          := tensor_obj) -- This notation is only temporary
-- curried tensor product of morphisms:
(tensor_hom               :
  Π {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂)))
(infixr ` ⊗' `:69         := tensor_hom) -- This notation is only temporary
-- tensor product laws:
(tensor_id'               :
  ∀ (X₁ X₂ : C), (𝟙 X₁) ⊗' (𝟙 X₂) = 𝟙 (X₁ ⊗ X₂) . obviously)
(tensor_comp'             :
  ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
  (f₁ ≫ g₁) ⊗' (f₂ ≫ g₂) = (f₁ ⊗' f₂) ≫ (g₁ ⊗' g₂) . obviously)
-- tensor unit:
(tensor_unit []           : C)
(notation `𝟙_`            := tensor_unit)
-- associator:
(associator               :
  Π X Y Z : C, (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z))
(notation `α_`            := associator)
(associator_naturality'   :
  ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
  ((f₁ ⊗' f₂) ⊗' f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗' (f₂ ⊗' f₃)) . obviously)
-- left unitor:
(left_unitor              : Π X : C, 𝟙_ ⊗ X ≅ X)
(notation `λ_`            := left_unitor)
(left_unitor_naturality'  :
  ∀ {X Y : C} (f : X ⟶ Y), ((𝟙 𝟙_) ⊗' f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f . obviously)
-- right unitor:
(right_unitor             : Π X : C, X ⊗ 𝟙_ ≅ X)
(notation `ρ_`            := right_unitor)
(right_unitor_naturality' :
  ∀ {X Y : C} (f : X ⟶ Y), (f ⊗' (𝟙 𝟙_)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f . obviously)
-- pentagon identity:
(pentagon'                : ∀ W X Y Z : C,
  ((α_ W X Y).hom ⊗' (𝟙 Z)) ≫ (α_ W (X ⊗ Y) Z).hom ≫ ((𝟙 W) ⊗' (α_ X Y Z).hom)
  = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom . obviously)
-- triangle identity:
(triangle'                :
  ∀ X Y : C, (α_ X 𝟙_ Y).hom ≫ ((𝟙 X) ⊗' (λ_ Y).hom) = (ρ_ X).hom ⊗' (𝟙 Y) . obviously)

restate_axiom monoidal_category.tensor_id'
attribute [simp] monoidal_category.tensor_id
restate_axiom monoidal_category.tensor_comp'
attribute [simp] monoidal_category.tensor_comp
restate_axiom monoidal_category.associator_naturality'
attribute [reassoc] monoidal_category.associator_naturality
restate_axiom monoidal_category.left_unitor_naturality'
attribute [reassoc] monoidal_category.left_unitor_naturality
restate_axiom monoidal_category.right_unitor_naturality'
attribute [reassoc] monoidal_category.right_unitor_naturality
restate_axiom monoidal_category.pentagon'
restate_axiom monoidal_category.triangle'
attribute [simp] monoidal_category.triangle

open monoidal_category

infixr ` ⊗ `:70 := tensor_obj
infixr ` ⊗ `:70 := tensor_hom

notation `𝟙_` := tensor_unit
notation `α_` := associator
notation `λ_` := left_unitor
notation `ρ_` := right_unitor

/-- The tensor product of two isomorphisms is an isomorphism. -/
def tensor_iso {C : Type u} {X Y X' Y' : C} [category.{v} C] [monoidal_category.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    X ⊗ X' ≅ Y ⊗ Y' :=
{ hom := f.hom ⊗ g.hom,
  inv := f.inv ⊗ g.inv,
  hom_inv_id' := by rw [←tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ←tensor_id],
  inv_hom_id' := by rw [←tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ←tensor_id] }

infixr ` ⊗ `:70 := tensor_iso

namespace monoidal_category

section

variables {C : Type u} [category.{v} C] [monoidal_category.{v} C]

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : is_iso (f ⊗ g) :=
{ ..(as_iso f ⊗ as_iso g) }

@[simp] lemma inv_tensor {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g := rfl

variables {U V W X Y Z : C}

-- When `rewrite_search` lands, add @[search] attributes to

-- monoidal_category.tensor_id monoidal_category.tensor_comp monoidal_category.associator_naturality
-- monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality
-- monoidal_category.pentagon monoidal_category.triangle

-- tensor_comp_id tensor_id_comp comp_id_tensor_tensor_id
-- triangle_assoc_comp_left triangle_assoc_comp_right triangle_assoc_comp_left_inv triangle_assoc_comp_right_inv
-- left_unitor_tensor left_unitor_tensor_inv
-- right_unitor_tensor right_unitor_tensor_inv
-- pentagon_inv
-- associator_inv_naturality
-- left_unitor_inv_naturality
-- right_unitor_inv_naturality

@[simp] lemma comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) :
  (f ≫ g) ⊗ (𝟙 Z) = (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) :=
by { rw ←tensor_comp, simp }

@[simp] lemma id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z) ⊗ (f ≫ g) = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
by { rw ←tensor_comp, simp }

@[simp] lemma id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = g ⊗ f :=
by { rw [←tensor_comp], simp }

@[simp] lemma tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) :
  (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) = g ⊗ f :=
by { rw [←tensor_comp], simp }

lemma left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) :=
begin
  apply (cancel_mono (λ_ X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  rw [left_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
end

lemma right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) :=
begin
  apply (cancel_mono (ρ_ X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  rw [right_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
end

@[simp] lemma tensor_left_iff
  {X Y : C} (f g : X ⟶ Y) :
  ((𝟙 (𝟙_ C)) ⊗ f = (𝟙 (𝟙_ C)) ⊗ g) ↔ (f = g) :=
begin
  split,
  { intro h,
    have h' := congr_arg (λ k, (λ_ _).inv ≫ k) h,
    dsimp at h',
    rw [←left_unitor_inv_naturality, ←left_unitor_inv_naturality] at h',
    exact (cancel_mono _).1 h', },
  { intro h, subst h, }
end

@[simp] lemma tensor_right_iff
  {X Y : C} (f g : X ⟶ Y) :
  (f ⊗ (𝟙 (𝟙_ C)) = g ⊗ (𝟙 (𝟙_ C))) ↔ (f = g) :=
begin
  split,
  { intro h,
    have h' := congr_arg (λ k, (ρ_ _).inv ≫ k) h,
    dsimp at h',
    rw [←right_unitor_inv_naturality, ←right_unitor_inv_naturality] at h',
    exact (cancel_mono _).1 h' },
  { intro h, subst h, }
end

-- We now prove:
--   ((α_ (𝟙_ C) X Y).hom) ≫
--     ((λ_ (X ⊗ Y)).hom)
--   = ((λ_ X).hom ⊗ (𝟙 Y))
-- (and the corresponding fact for right unitors)
-- following the proof on nLab:
-- Lemma 2.2 at <https://ncatlab.org/nlab/revision/monoidal+category/115>

lemma left_unitor_product_aux_perimeter (X Y : C) :
    ((α_ (𝟙_ C) (𝟙_ C) X).hom ⊗ (𝟙 Y)) ≫
    (α_ (𝟙_ C) ((𝟙_ C) ⊗ X) Y).hom ≫
    ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) X Y).hom) ≫
    ((𝟙 (𝟙_ C)) ⊗ (λ_ (X ⊗ Y)).hom)
  = (((ρ_ (𝟙_ C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y)) ≫
    (α_ (𝟙_ C) X Y).hom :=
begin
  conv_lhs { congr, skip, rw [←category.assoc] },
  rw [←category.assoc, monoidal_category.pentagon, associator_naturality, tensor_id,
      ←monoidal_category.triangle, ←category.assoc]
end

lemma left_unitor_product_aux_triangle (X Y : C) :
    ((α_ (𝟙_ C) (𝟙_ C) X).hom ⊗ (𝟙 Y)) ≫
    (((𝟙 (𝟙_ C)) ⊗ (λ_ X).hom) ⊗ (𝟙 Y))
  = ((ρ_ (𝟙_ C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y) :=
by rw [←comp_tensor_id, ←monoidal_category.triangle]

lemma left_unitor_product_aux_square (X Y : C) :
    (α_ (𝟙_ C) ((𝟙_ C) ⊗ X) Y).hom ≫
    ((𝟙 (𝟙_ C)) ⊗ (λ_ X).hom ⊗ (𝟙 Y))
  = (((𝟙 (𝟙_ C)) ⊗ (λ_ X).hom) ⊗ (𝟙 Y)) ≫
    (α_ (𝟙_ C) X Y).hom :=
by rw associator_naturality

lemma left_unitor_product_aux (X Y : C) :
    ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) X Y).hom) ≫
    ((𝟙 (𝟙_ C)) ⊗ (λ_ (X ⊗ Y)).hom)
  = (𝟙 (𝟙_ C)) ⊗ ((λ_ X).hom ⊗ (𝟙 Y)) :=
begin
  rw ←(cancel_epi (α_ (𝟙_ C) ((𝟙_ C) ⊗ X) Y).hom),
  rw left_unitor_product_aux_square,
  rw ←(cancel_epi ((α_ (𝟙_ C) (𝟙_ C) X).hom ⊗ (𝟙 Y))),
  slice_rhs 1 2 { rw left_unitor_product_aux_triangle },
  conv_lhs { rw [left_unitor_product_aux_perimeter] }
end

lemma right_unitor_product_aux_perimeter (X Y : C) :
    ((α_ X Y (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫
    (α_ X (Y ⊗ (𝟙_ C)) (𝟙_ C)).hom ≫
    ((𝟙 X) ⊗ (α_ Y (𝟙_ C) (𝟙_ C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (λ_ (𝟙_ C)).hom)
  = ((ρ_ (X ⊗ Y)).hom ⊗ (𝟙 (𝟙_ C))) ≫
    (α_ X Y (𝟙_ C)).hom :=
begin
  transitivity (((α_ X Y _).hom ⊗ 𝟙 _) ≫ (α_ X _ _).hom ≫
    (𝟙 X ⊗ (α_ Y _ _).hom)) ≫
    (𝟙 X ⊗ 𝟙 Y ⊗ (λ_ _).hom),
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
    ((𝟙 X) ⊗ (α_ Y (𝟙_ C) (𝟙_ C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (λ_ (𝟙_ C)).hom)
  = (𝟙 X) ⊗ (ρ_ Y).hom ⊗ (𝟙 (𝟙_ C)) :=
by rw [←id_tensor_comp, ←monoidal_category.triangle]

lemma right_unitor_product_aux_square (X Y : C) :
    (α_ X (Y ⊗ (𝟙_ C)) (𝟙_ C)).hom ≫
    ((𝟙 X) ⊗ (ρ_ Y).hom ⊗ (𝟙 (𝟙_ C)))
  = (((𝟙 X) ⊗ (ρ_ Y).hom) ⊗ (𝟙 (𝟙_ C))) ≫
    (α_ X Y (𝟙_ C)).hom :=
by rw [associator_naturality]

lemma right_unitor_product_aux (X Y : C) :
    ((α_ X Y (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫
    (((𝟙 X) ⊗ (ρ_ Y).hom) ⊗ (𝟙 (𝟙_ C)))
  = ((ρ_ (X ⊗ Y)).hom ⊗ (𝟙 (𝟙_ C))) :=
begin
  rw ←(cancel_mono (α_ X Y (𝟙_ C)).hom),
  slice_lhs 2 3 { rw ←right_unitor_product_aux_square },
  rw [←right_unitor_product_aux_triangle, ←right_unitor_product_aux_perimeter],
end

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[simp] lemma left_unitor_tensor (X Y : C) :
  ((α_ (𝟙_ C) X Y).hom) ≫ ((λ_ (X ⊗ Y)).hom) =
    ((λ_ X).hom ⊗ (𝟙 Y)) :=
by rw [←tensor_left_iff, id_tensor_comp, left_unitor_product_aux]

@[simp] lemma left_unitor_tensor_inv (X Y : C) :
  ((λ_ (X ⊗ Y)).inv) ≫ ((α_ (𝟙_ C) X Y).inv) =
    ((λ_ X).inv ⊗ (𝟙 Y)) :=
eq_of_inv_eq_inv (by simp)

@[simp] lemma right_unitor_tensor (X Y : C) :
  ((α_ X Y (𝟙_ C)).hom) ≫ ((𝟙 X) ⊗ (ρ_ Y).hom) =
    ((ρ_ (X ⊗ Y)).hom) :=
by rw [←tensor_right_iff, comp_tensor_id, right_unitor_product_aux]

@[simp] lemma right_unitor_tensor_inv (X Y : C) :
  ((𝟙 X) ⊗ (ρ_ Y).inv) ≫ ((α_ X Y (𝟙_ C)).inv) =
    ((ρ_ (X ⊗ Y)).inv) :=
eq_of_inv_eq_inv (by simp)

lemma associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
  (f ⊗ (g ⊗ h)) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
begin
  apply (cancel_mono (α_ X' Y' Z').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  rw [associator_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
end

lemma pentagon_inv (W X Y Z : C) :
  ((𝟙 W) ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ (𝟙 Z))
    = (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
begin
  apply category_theory.eq_of_inv_eq_inv,
  dsimp,
  rw [category.assoc, monoidal_category.pentagon]
end

lemma triangle_assoc_comp_left (X Y : C) :
  (α_ X (𝟙_ C) Y).hom ≫ ((𝟙 X) ⊗ (λ_ Y).hom) = (ρ_ X).hom ⊗ 𝟙 Y :=
monoidal_category.triangle X Y

@[simp] lemma triangle_assoc_comp_right (X Y : C) :
  (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ⊗ 𝟙 Y) = ((𝟙 X) ⊗ (λ_ Y).hom) :=
by rw [←triangle_assoc_comp_left, ←category.assoc, iso.inv_hom_id, category.id_comp]

@[simp] lemma triangle_assoc_comp_right_inv (X Y : C) :
  ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X (𝟙_ C) Y).hom = ((𝟙 X) ⊗ (λ_ Y).inv) :=
begin
  apply (cancel_mono (𝟙 X ⊗ (λ_ Y).hom)).1,
  simp only [assoc, triangle_assoc_comp_left],
  rw [←comp_tensor_id, iso.inv_hom_id, ←id_tensor_comp, iso.inv_hom_id]
end

@[simp] lemma triangle_assoc_comp_left_inv (X Y : C) :
  ((𝟙 X) ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = ((ρ_ X).inv ⊗ 𝟙 Y) :=
begin
  apply (cancel_mono ((ρ_ X).hom ⊗ 𝟙 Y)).1,
  simp only [triangle_assoc_comp_right, assoc],
  rw [←id_tensor_comp, iso.inv_hom_id, ←comp_tensor_id, iso.inv_hom_id]
end

end

section
variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

/-- The tensor product expressed as a functor. -/
def tensor : (C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), f.1 ⊗ f.2 }

/-- The left-associated triple tensor product as a functor. -/
def left_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, (X.1 ⊗ X.2.1) ⊗ X.2.2,
  map := λ {X Y : C × C × C} (f : X ⟶ Y), (f.1 ⊗ f.2.1) ⊗ f.2.2 }

@[simp] lemma left_assoc_tensor_obj (X) :
  (left_assoc_tensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 := rfl
@[simp] lemma left_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (left_assoc_tensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 := rfl

/-- The right-associated triple tensor product as a functor. -/
def right_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ (X.2.1 ⊗ X.2.2),
  map := λ {X Y : C × C × C} (f : X ⟶ Y), f.1 ⊗ (f.2.1 ⊗ f.2.2) }

@[simp] lemma right_assoc_tensor_obj (X) :
  (right_assoc_tensor C).obj X = X.1 ⊗ (X.2.1 ⊗ X.2.2) := rfl
@[simp] lemma right_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (right_assoc_tensor C).map f = f.1 ⊗ (f.2.1 ⊗ f.2.2) := rfl

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensor_unit_left : C ⥤ C :=
{ obj := λ X, 𝟙_ C ⊗ X,
  map := λ {X Y : C} (f : X ⟶ Y), (𝟙 (𝟙_ C)) ⊗ f }
/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensor_unit_right : C ⥤ C :=
{ obj := λ X, X ⊗ 𝟙_ C,
  map := λ {X Y : C} (f : X ⟶ Y), f ⊗ (𝟙 (𝟙_ C)) }

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.

/-- The associator as a natural isomorphism. -/
def associator_nat_iso :
  left_assoc_tensor C ≅ right_assoc_tensor C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.associator })
  (by { intros, apply monoidal_category.associator_naturality })

/-- The left unitor as a natural isomorphism. -/
def left_unitor_nat_iso :
  tensor_unit_left C ≅ 𝟭 C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.left_unitor })
  (by { intros, apply monoidal_category.left_unitor_naturality })

/-- The right unitor as a natural isomorphism. -/
def right_unitor_nat_iso :
  tensor_unit_right C ≅ 𝟭 C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.right_unitor })
  (by { intros, apply monoidal_category.right_unitor_naturality })



section
variables {C}

/-- Tensoring on the left with as fixed object, as a functor. -/
@[simps]
def tensor_left (X : C) : C ⥤ C :=
{ obj := λ Y, X ⊗ Y,
  map := λ Y Y' f, (𝟙 X) ⊗ f, }

/--
Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensor_left_tensor (X Y : C) : tensor_left (X ⊗ Y) ≅ tensor_left Y ⋙ tensor_left X :=
nat_iso.of_components
  (associator _ _)
  (λ Z Z' f, by { dsimp, rw[←tensor_id], apply associator_naturality })

@[simp] lemma tensor_left_tensor_hom_app (X Y Z : C) :
  (tensor_left_tensor X Y).hom.app Z = (associator X Y Z).hom :=
rfl
@[simp] lemma tensor_left_tensor_inv_app (X Y Z : C) :
  (tensor_left_tensor X Y).inv.app Z = (associator X Y Z).inv :=
rfl

/-- Tensoring on the right with as fixed object, as a functor. -/
@[simps]
def tensor_right (X : C) : C ⥤ C :=
{ obj := λ Y, Y ⊗ X,
  map := λ Y Y' f, f ⊗ (𝟙 X), }

/--
Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensor_right_tensor (X Y : C) : tensor_right (X ⊗ Y) ≅ tensor_right X ⋙ tensor_right Y :=
nat_iso.of_components
  (λ Z, (associator Z X Y).symm)
  (λ Z Z' f, by { dsimp, rw[←tensor_id], apply associator_inv_naturality })

@[simp] lemma tensor_right_tensor_hom_app (X Y Z : C) :
  (tensor_right_tensor X Y).hom.app Z = (associator Z X Y).inv :=
rfl
@[simp] lemma tensor_right_tensor_inv_app (X Y Z : C) :
  (tensor_right_tensor X Y).inv.app Z = (associator Z X Y).hom :=
rfl

end

end

end monoidal_category

end category_theory
