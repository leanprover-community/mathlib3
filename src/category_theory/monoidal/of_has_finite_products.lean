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

end

namespace has_binary_products
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

end has_binary_products

section has_terminal

open has_binary_products

variables {C}
variables [has_binary_products C]
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

end has_terminal

namespace has_binary_coproducts

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

end has_binary_coproducts

namespace has_initial

open has_binary_coproducts

variables {C}
variables [has_binary_coproducts C]
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

end has_initial

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

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products :
  monoidal_category C :=
{ tensor_unit  := 𝒯.cone.X,
  tensor_obj   := λ X Y, tensor_obj ℬ X Y,
  tensor_hom   := λ _ _ _ _ f g, tensor_hom ℬ f g,
  tensor_id'   := sorry,
  tensor_comp' := sorry,
  associator   := λ X Y Z, prod.assoc_of_limit_data ℬ X Y Z,
  left_unitor  := sorry,
  right_unitor := sorry,
  pentagon'    := sorry,
  triangle'    := sorry,
  associator_naturality' := begin extract_goal, sorry, end, }
end

section
local attribute [instance] monoidal_of_has_finite_products

open monoidal_category

/--
The monoidal structure coming from finite products is symmetric.
-/
@[simps]
def symmetric_of_has_finite_products [has_terminal C] [has_binary_products C] :
  symmetric_category C :=
{ braiding := limits.prod.braiding,
  braiding_naturality' := λ X X' Y Y' f g,
    by { dsimp [tensor_hom], ext; simp, },
  hexagon_forward' := λ X Y Z,
    by ext; { dsimp [monoidal_of_has_finite_products], simp; dsimp; simp, },
  hexagon_reverse' := λ X Y Z,
    by ext; { dsimp [monoidal_of_has_finite_products], simp; dsimp; simp, },
  symmetry' := λ X Y, by { dsimp, simp, refl, }, }

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


section
local attribute [instance] monoidal_of_has_finite_coproducts

open monoidal_category

/--
The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps]
def symmetric_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] :
  symmetric_category C :=
{ braiding := limits.coprod.braiding,
  braiding_naturality' := λ X X' Y Y' f g,
    by { dsimp [tensor_hom], ext; simp, },
  hexagon_forward' := λ X Y Z,
    by ext; { dsimp [monoidal_of_has_finite_coproducts], simp; dsimp; simp, },
  hexagon_reverse' := λ X Y Z,
    by ext; { dsimp [monoidal_of_has_finite_coproducts], simp; dsimp; simp, },
  symmetry' := λ X Y, by { dsimp, simp, refl, }, }

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
