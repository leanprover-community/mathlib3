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

open walking_pair

instance fintype_walking_pair : fintype walking_pair :=
{ elems := [left, right].to_finset,
  complete := λ x, by { cases x; simp } }

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : discrete walking_pair ⥤ C :=
functor.of_function (λ j, walking_pair.cases_on j X Y)

@[simp] lemma pair_obj_left (X Y : C) : (pair X Y).obj left = X := rfl
@[simp] lemma pair_obj_right (X Y : C) : (pair X Y).obj right = Y := rfl

section
variables {F G : discrete walking_pair.{v} ⥤ C} (f : F.obj left ⟶ G.obj left) (g : F.obj right ⟶ G.obj right)

/-- The natural transformation between two functors out of the walking pair, specified by its components. -/
def map_pair : F ⟶ G :=
{ app := λ j, match j with
  | left := f
  | right := g
  end }

@[simp] lemma map_pair_left : (map_pair f g).app left = f := rfl
@[simp] lemma map_pair_right : (map_pair f g).app right = g := rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its components. -/
@[simps]
def map_pair_iso (f : F.obj left ≅ G.obj left) (g : F.obj right ≅ G.obj right) : F ≅ G :=
{ hom := map_pair f.hom g.hom,
  inv := map_pair f.inv g.inv,
  hom_inv_id' := begin ext j, cases j; { dsimp, simp, } end,
  inv_hom_id' := begin ext j, cases j; { dsimp, simp, } end }
end

section
variables {D : Type u} [𝒟 : category.{v} D]
include 𝒟

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pair_comp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
map_pair_iso (eq_to_iso rfl) (eq_to_iso rfl)
end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
def diagram_iso_pair (F : discrete walking_pair ⥤ C) :
  F ≅ pair (F.obj walking_pair.left) (F.obj walking_pair.right) :=
map_pair_iso (eq_to_iso rfl) (eq_to_iso rfl)

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
@[simp] lemma binary_cofan.mk_ι_app_left {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.left = ι₁ := rfl
@[simp] lemma binary_cofan.mk_ι_app_right {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.right = ι₂ := rfl

abbreviation prod (X Y : C) [has_limit (pair X Y)] := limit (pair X Y)
abbreviation coprod (X Y : C) [has_colimit (pair X Y)] := colimit (pair X Y)

notation X ` ⨯ `:20 Y:20 := prod X Y
notation X ` ⨿ `:20 Y:20 := coprod X Y

abbreviation prod.fst {X Y : C} [has_limit (pair X Y)] : X ⨯ Y ⟶ X :=
limit.π (pair X Y) walking_pair.left
abbreviation prod.snd {X Y : C} [has_limit (pair X Y)] : X ⨯ Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right
abbreviation coprod.inl {X Y : C} [has_colimit (pair X Y)] : X ⟶ X ⨿ Y :=
colimit.ι (pair X Y) walking_pair.left
abbreviation coprod.inr {X Y : C} [has_colimit (pair X Y)] : Y ⟶ X ⨿ Y :=
colimit.ι (pair X Y) walking_pair.right

abbreviation prod.lift {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
limit.lift _ (binary_fan.mk f g)
abbreviation coprod.desc {W X Y : C} [has_colimit (pair X Y)] (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

instance prod.mono_lift_of_mono_left {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y)
  [mono f] : mono (prod.lift f g) :=
mono_of_mono_fac $ show prod.lift f g ≫ prod.fst = f, by simp

instance prod.mono_lift_of_mono_right {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y)
  [mono g] : mono (prod.lift f g) :=
mono_of_mono_fac $ show prod.lift f g ≫ prod.snd = g, by simp

instance coprod.epi_desc_of_epi_left {W X Y : C} [has_colimit (pair X Y)] (f : X ⟶ W) (g : Y ⟶ W)
  [epi f] : epi (coprod.desc f g) :=
epi_of_epi_fac $ show coprod.inl ≫ coprod.desc f g = f, by simp

instance coprod.epi_desc_of_epi_right {W X Y : C} [has_colimit (pair X Y)] (f : X ⟶ W) (g : Y ⟶ W)
  [epi g] : epi (coprod.desc f g) :=
epi_of_epi_fac $ show coprod.inr ≫ coprod.desc f g = g, by simp

abbreviation prod.map {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
lim.map (map_pair f g)
abbreviation coprod.map {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
colim.map (map_pair f g)

variables (C)

class has_binary_products :=
(has_limits_of_shape : has_limits_of_shape.{v} (discrete walking_pair) C)
class has_binary_coproducts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} (discrete walking_pair) C)

attribute [instance] has_binary_products.has_limits_of_shape has_binary_coproducts.has_colimits_of_shape

@[priority 100] -- see Note [lower instance priority]
instance [has_finite_products.{v} C] : has_binary_products.{v} C :=
{ has_limits_of_shape := by apply_instance }
@[priority 100] -- see Note [lower instance priority]
instance [has_finite_coproducts.{v} C] : has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := by apply_instance }

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
def has_binary_products_of_has_limit_pair [Π {X Y : C}, has_limit (pair X Y)] :
  has_binary_products.{v} C :=
{ has_limits_of_shape := { has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm } }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
def has_binary_coproducts_of_has_colimit_pair [Π {X Y : C}, has_colimit (pair X Y)] :
  has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := { has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) } }

@[ext] lemma prod.hom_ext [has_binary_products.{v} C] {Y A B : C} {a b : Y ⟶ A ⨯ B}
  (h1 : a ≫ prod.fst = b ≫ prod.fst) (h2 : a ≫ prod.snd = b ≫ prod.snd) : a = b :=
limit.hom_ext (by rintros (_ | _); simpa)

@[simp, reassoc]
lemma prod.lift_fst [has_binary_products.{v} C] {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) :
  prod.lift f g ≫ prod.fst = f :=
limit.lift_π _ _

@[simp, reassoc]
lemma prod.lift_snd {Y A B : C} [has_binary_products.{v} C] (f : Y ⟶ A) (g : Y ⟶ B) :
  prod.lift f g ≫ prod.snd = g :=
limit.lift_π _ _

@[ext] lemma coprod.hom_ext [has_binary_coproducts.{v} C] {Y A B : C} {a b : A ⨿ B ⟶ Y}
  (h1 : coprod.inl ≫ a = coprod.inl ≫ b) (h2 : coprod.inr ≫ a = coprod.inr ≫ b) : a = b :=
colimit.hom_ext (by rintros (_ | _); simpa)

@[simp, reassoc]
lemma coprod.inl_desc [has_binary_coproducts.{v} C] {Y A B : C} (f : A ⟶ Y) (g : B ⟶ Y) :
  coprod.inl ≫ coprod.desc f g = f :=
colimit.ι_desc _ _

@[simp, reassoc]
lemma coprod.inr_desc {Y A B : C} [has_binary_coproducts.{v} C] (f : A ⟶ Y) (g : B ⟶ Y) :
  coprod.inr ≫ coprod.desc f g = g :=
colimit.ι_desc _ _

section

variables {C} [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

/-- The braiding isomorphism which swaps a binary product. -/
@[simps] def prod.braiding (P Q : C) : P ⨯ Q ≅ Q ⨯ P :=
{ hom := prod.lift prod.snd prod.fst,
  inv := prod.lift prod.snd prod.fst }

@[simp] lemma prod.symmetry' (P Q : C) :
  prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
lemma prod.symmetry (P Q : C) :
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

lemma prod.pentagon (W X Y Z : C) :
  prod.map ((prod.associator W X Y).hom) (𝟙 Z) ≫
      (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) ((prod.associator X Y Z).hom) =
    (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y⨯Z)).hom :=
by tidy

lemma prod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
    (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) :=
by tidy

variables [has_terminal.{v} C]

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

lemma prod.triangle (X Y : C) :
  (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) ((prod.left_unitor Y).hom) =
    prod.map ((prod.right_unitor X).hom) (𝟙 Y) :=
by tidy

end

section
variables {C} [has_binary_coproducts.{v} C]

local attribute [tidy] tactic.case_bash

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
      (coprod.associator W (X⨿Y) Z).hom ≫ coprod.map (𝟙 W) ((coprod.associator X Y Z).hom) =
    (coprod.associator (W⨿X) Y Z).hom ≫ (coprod.associator W X (Y⨿Z)).hom :=
by tidy

lemma coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
    (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) :=
by tidy

variables [has_initial.{v} C]

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

end category_theory.limits
