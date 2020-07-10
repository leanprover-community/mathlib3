/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.category
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal

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

namespace category_theory

variables (C : Type u) [category.{v} C] {X Y : C}

namespace limits

section
variables {C} [has_binary_products C]

/-- The braiding isomorphism which swaps a binary product. -/
@[simps] def prod.braiding (P Q : C) : P ⨯ Q ≅ Q ⨯ P :=
{ hom := prod.lift prod.snd prod.fst,
  inv := prod.lift prod.snd prod.fst }

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc] lemma braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
  prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f :=
by tidy

@[simp, reassoc] lemma prod.symmetry' (P Q : C) :
  prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
@[reassoc] lemma prod.symmetry (P Q : C) :
  (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
by simp

/-- The associator isomorphism for binary products. -/
@[simps] def prod.associator
  (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ (Q ⨯ R) :=
{ hom :=
  prod.lift
    (prod.fst ≫ prod.fst)
    (prod.lift (prod.fst ≫ prod.snd) prod.snd),
  inv :=
  prod.lift
    (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.snd ≫ prod.snd) }

/-- The product functor can be decomposed. -/
def prod_functor_left_comp (X Y : C) :
  prod_functor.obj (X ⨯ Y) ≅ prod_functor.obj Y ⋙ prod_functor.obj X :=
nat_iso.of_components (prod.associator _ _) (by tidy)

@[reassoc]
lemma prod.pentagon (W X Y Z : C) :
  prod.map ((prod.associator W X Y).hom) (𝟙 Z) ≫
      (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) ((prod.associator X Y Z).hom) =
    (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom :=
by tidy

@[reassoc]
lemma prod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
    (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) :=
by tidy



variables [has_terminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps] def prod.left_unitor
  (P : C) : ⊤_ C ⨯ P ≅ P :=
{ hom := prod.snd,
  inv := prod.lift (terminal.from P) (𝟙 _) }

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps] def prod.right_unitor
  (P : C) : P ⨯ ⊤_ C ≅ P :=
{ hom := prod.fst,
  inv := prod.lift (𝟙 _) (terminal.from P) }

@[reassoc]
lemma prod_left_unitor_hom_naturality (f : X ⟶ Y):
  prod.map (𝟙 _) f ≫ (prod.left_unitor Y).hom = (prod.left_unitor X).hom ≫ f :=
prod.map_snd _ _

@[reassoc]
lemma prod_left_unitor_inv_naturality (f : X ⟶ Y):
  (prod.left_unitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.left_unitor Y).inv :=
by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod_left_unitor_hom_naturality]

@[reassoc]
lemma prod_right_unitor_hom_naturality (f : X ⟶ Y):
  prod.map f (𝟙 _) ≫ (prod.right_unitor Y).hom = (prod.right_unitor X).hom ≫ f :=
prod.map_fst _ _

@[reassoc]
lemma prod_right_unitor_inv_naturality (f : X ⟶ Y):
  (prod.right_unitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.right_unitor Y).inv :=
by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod_right_unitor_hom_naturality]

lemma prod.triangle (X Y : C) :
  (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) ((prod.left_unitor Y).hom) =
    prod.map ((prod.right_unitor X).hom) (𝟙 Y) :=
by tidy

end

section
variables {C} [has_binary_coproducts C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps] def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P :=
{ hom := coprod.desc coprod.inr coprod.inl,
  inv := coprod.desc coprod.inr coprod.inl }

@[simp] lemma coprod.symmetry' (P Q : C) :
  coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
lemma coprod.symmetry (P Q : C) :
  (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
by simp

/-- The associator isomorphism for binary coproducts. -/
@[simps] def coprod.associator
  (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ (Q ⨿ R) :=
{ hom :=
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr),
  inv :=
  coprod.desc
    (coprod.inl ≫ coprod.inl)
    (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) }

lemma coprod.pentagon (W X Y Z : C) :
  coprod.map ((coprod.associator W X Y).hom) (𝟙 Z) ≫
      (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) ((coprod.associator X Y Z).hom) =
    (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom :=
by tidy

lemma coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
    (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) :=
by tidy

variables [has_initial C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps] def coprod.left_unitor
  (P : C) : ⊥_ C ⨿ P ≅ P :=
{ hom := coprod.desc (initial.to P) (𝟙 _),
  inv := coprod.inr }

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps] def coprod.right_unitor
  (P : C) : P ⨿ ⊥_ C ≅ P :=
{ hom := coprod.desc (𝟙 _) (initial.to P),
  inv := coprod.inl }

lemma coprod.triangle (X Y : C) :
  (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) ((coprod.left_unitor Y).hom) =
    coprod.map ((coprod.right_unitor X).hom) (𝟙 Y) :=
by tidy

end
end limits

open category_theory.limits

section
local attribute [tidy] tactic.case_bash

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products [has_terminal C] [has_binary_products C] : monoidal_category C :=
{ tensor_unit  := ⊤_ C,
  tensor_obj   := λ X Y, X ⨯ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.prod.map f g,
  associator   := prod.associator,
  left_unitor  := prod.left_unitor,
  right_unitor := prod.right_unitor,
  pentagon'    := prod.pentagon,
  triangle'    := prod.triangle,
  associator_naturality' := @prod.associator_naturality _ _ _, }
end

namespace monoidal_of_has_finite_products

variables [has_terminal C] [has_binary_products C]
local attribute [instance] monoidal_of_has_finite_products

@[simp]
lemma tensor_obj (X Y : C) : X ⊗ Y = (X ⨯ Y) := rfl
@[simp]
lemma tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.prod.map f g := rfl

@[simp]
lemma left_unitor_hom (X : C) : (λ_ X).hom = limits.prod.snd := rfl
@[simp]
lemma left_unitor_inv (X : C) : (λ_ X).inv = prod.lift (terminal.from X) (𝟙 _) := rfl
@[simp]
lemma right_unitor_hom (X : C) : (ρ_ X).hom = limits.prod.fst := rfl
@[simp]
lemma right_unitor_inv (X : C) : (ρ_ X).inv = prod.lift (𝟙 _) (terminal.from X) := rfl
-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
lemma associator_hom (X Y Z : C) :
  (α_ X Y Z).hom =
  prod.lift
    (limits.prod.fst ≫ limits.prod.fst)
    (prod.lift (limits.prod.fst ≫ limits.prod.snd) limits.prod.snd) := rfl

end monoidal_of_has_finite_products

section
local attribute [tidy] tactic.case_bash

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidal_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] : monoidal_category C :=
{ tensor_unit  := ⊥_ C,
  tensor_obj   := λ X Y, X ⨿ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.coprod.map f g,
  associator   := coprod.associator,
  left_unitor  := coprod.left_unitor,
  right_unitor := coprod.right_unitor,
  pentagon'    := coprod.pentagon,
  triangle'    := coprod.triangle,
  associator_naturality' := @coprod.associator_naturality _ _ _, }
end

namespace monoidal_of_has_finite_coproducts

variables [has_initial C] [has_binary_coproducts C]
local attribute [instance] monoidal_of_has_finite_coproducts

@[simp]
lemma tensor_obj (X Y : C) : X ⊗ Y = (X ⨿ Y) := rfl
@[simp]
lemma tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.coprod.map f g := rfl

@[simp]
lemma left_unitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) := rfl
@[simp]
lemma right_unitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) := rfl
@[simp]
lemma left_unitor_inv (X : C) : (λ_ X).inv = limits.coprod.inr := rfl
@[simp]
lemma right_unitor_inv (X : C) : (ρ_ X).inv = limits.coprod.inl := rfl
-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
lemma associator_hom (X Y Z : C) :
  (α_ X Y Z).hom =
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr) := rfl

end monoidal_of_has_finite_coproducts

end category_theory

-- TODO in fact, a category with finite products is braided, and symmetric,
-- and we should say that here, once braided categories arrive in mathlib.
