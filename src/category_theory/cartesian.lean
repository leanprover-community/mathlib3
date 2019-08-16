import .tac
import category_theory.monoidal.category
import category_theory.opposites

universes v u

namespace category_theory

class cartesian_category (C : Type u) [category.{v} C] :=
(prod_obj : C → C → C)
(infixr ` π `:70          := prod_obj)
(one : C)
(prod_hom :
  Π {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (X₁ π X₂ ⟶ Y₁ π Y₂))
(prod_elim_left :
  Π Y₁ Y₂ : C, (Y₁ π Y₂) ⟶ Y₁)
(prod_elim_right :
  Π Y₁ Y₂ : C, (Y₁ π Y₂) ⟶ Y₂)
(prod_intro :
  Π {X Y₁ Y₂ : C}, (X ⟶ Y₁) → (X ⟶ Y₂) → (X ⟶ Y₁ π Y₂))
(prod_intro_elim_left :
  Π {X Y₁ Y₂ : C} (f : X ⟶ Y₁) (g : X ⟶ Y₂),
    prod_intro f g ≫ prod_elim_left Y₁ Y₂ = f  . obviously)
(prod_intro_elim_right :
  Π {X Y₁ Y₂ : C} (f : X ⟶ Y₁) (g : X ⟶ Y₂),
    prod_intro f g ≫ prod_elim_right Y₁ Y₂ = g  . obviously)
(prod_intro_comp :
  Π {X Y₁ Y₂ : C} (f : X ⟶ Y₁ π Y₂),
    prod_intro (f ≫ prod_elim_left Y₁ Y₂) (f ≫ prod_elim_right Y₁ Y₂) = f . obviously)
(hom_elim_left :
  Π {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    prod_hom f g ≫ prod_elim_left Y₁ Y₂ = prod_elim_left X₁ X₂ ≫ f  . obviously)
(hom_elim_right :
  Π {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    prod_hom f g ≫ prod_elim_right Y₁ Y₂ = prod_elim_right X₁ X₂ ≫ g  . obviously)
(prod_intro_hom :
  Π {X₁ X₂ Y₁ Y₂ Z : C} (f : Z ⟶ X₁) (g : Z ⟶ X₂) (f' : X₁ ⟶ Y₁) (g' : X₂ ⟶ Y₂),
    prod_intro f g ≫ prod_hom f' g' = prod_intro (f ≫ f') (g ≫ g')  . obviously)
(intro : Π x : C, x ⟶ one)
(intro_unique : Π x (f : x ⟶ one), f = intro x . obviously)

namespace cartesian_category
attribute [simp] prod_intro_hom hom_elim_right hom_elim_left prod_intro_comp prod_intro_elim_right prod_intro_elim_left
reassoc_axiom cartesian_category.prod_intro_elim_left
reassoc_axiom prod_intro_elim_right
reassoc_axiom hom_elim_left
reassoc_axiom hom_elim_right
reassoc_axiom prod_intro_hom
end cartesian_category

class cocartesian_category (C : Type u) [category.{v} C] :=
(coprod_obj : C → C → C)
(infixr ` ⨿ `:70          := coprod_obj)
(zero : C)
(coprod_hom :
  Π {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (X₁ ⨿ X₂ ⟶ Y₁ ⨿ Y₂))
(coprod_intro_left :
  Π Y₁ Y₂ : C, Y₁ ⟶ (Y₁ ⨿ Y₂))
(coprod_intro_right :
  Π Y₁ Y₂ : C, Y₂ ⟶ (Y₁ ⨿ Y₂))
(coprod_elim :
  Π {X₁ X₂ Y : C}, (X₁ ⟶ Y) → (X₂ ⟶ Y) → (X₁ ⨿ X₂ ⟶ Y))
(coprod_intro_left_elim :
  Π {X₁ X₂ Y : C} (f : X₁ ⟶ Y) (g : X₂ ⟶ Y),
    coprod_intro_left X₁ X₂ ≫ coprod_elim f g = f . obviously)
(coprod_intro_right_elim :
  Π {X₁ X₂ Y : C} (f : X₁ ⟶ Y) (g : X₂ ⟶ Y),
    coprod_intro_right X₁ X₂ ≫ coprod_elim f g = g . obviously)
(coprod_elim_comp :
  Π {X₁ X₂ Y : C} (f : X₁ ⨿ X₂ ⟶ Y),
    coprod_elim (coprod_intro_left X₁ X₂ ≫ f) (coprod_intro_right X₁ X₂ ≫ f) = f . obviously)
(intro_left_hom :
  Π {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    coprod_intro_left X₁ X₂ ≫ coprod_hom f g = f ≫ coprod_intro_left Y₁ Y₂  . obviously)
(intro_right_hom :
  Π {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    coprod_intro_right X₁ X₂ ≫ coprod_hom f g = g ≫ coprod_intro_right Y₁ Y₂  . obviously)
(coprod_hom_elim :
  Π {X₁ X₂ Y₁ Y₂ Z : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (f' : Y₁ ⟶ Z) (g' : Y₂ ⟶ Z),
    coprod_hom f g ≫ coprod_elim f' g' = coprod_elim (f ≫ f') (g ≫ g')  . obviously)
(elim : Π x, zero ⟶ x)
(elim_unique : Π x (f : zero ⟶ x), f = elim x . obviously)

namespace cocartesian_category
attribute [simp] coprod_hom_elim intro_right_hom intro_left_hom coprod_elim_comp coprod_intro_right_elim coprod_intro_left_elim
reassoc_axiom coprod_hom_elim
reassoc_axiom intro_right_hom
reassoc_axiom intro_left_hom
reassoc_axiom coprod_intro_right_elim
reassoc_axiom coprod_intro_left_elim
end cocartesian_category

variables {C : Type u}
variables [𝒞 : category.{v} C]
include 𝒞
open opposite

namespace cartesian_category
variables [𝒟 : cartesian_category.{v} C]
include 𝒟
infixr ` π `:70          := prod_obj
infixr ` π `:70          := prod_hom

variables {X₁ X₂ Y₁ Y₂ Z W : C}

lemma prod_hom_def (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  f π g = prod_intro (prod_elim_left _ _ ≫ f) (prod_elim_right _ _ ≫ g) :=
begin
  rw [← hom_elim_left _ f g,← hom_elim_right _ f g,prod_intro_comp]
end

@[extensionality]
lemma ext (f g : Z ⟶ X₁ π X₂)
  (h₀ : f ≫ prod_elim_left _ _ = g ≫ prod_elim_left _ _)
  (h₁ : f ≫ prod_elim_right _ _ = g ≫ prod_elim_right _ _) :
  f = g :=
begin
  transitivity prod_intro (f ≫ prod_elim_left X₁ X₂) (f ≫ prod_elim_right X₁ X₂),
  rw prod_intro_comp,
  rw [h₀,h₁,prod_intro_comp],
end

@[simp]
lemma prod_intro_comp' (f : Z ⟶ W) (g : W ⟶ X₁) (h : W ⟶ X₂) : f ≫ prod_intro g h = prod_intro (f ≫ g) (f ≫ h) :=
ext _ _
  (by rw [prod_intro_elim_left,category.assoc,prod_intro_elim_left])
  (by rw [prod_intro_elim_right,category.assoc,prod_intro_elim_right])

@[simp]
lemma intro_unique' (f f' : Z ⟶ one C) : f = f' ↔ true := by simp [intro_unique _ _ f,intro_unique _ _ f']

@[simp]
lemma comp_intro {X Y : C} (f : X ⟶ Y) : f ≫ intro Y = intro X := intro_unique _ _ _

@[simp]
lemma intro_elim_elim {X Y : C} : prod_intro (prod_elim_left X Y) (prod_elim_right X Y) = 𝟙 (X π Y) :=
by ext; simp

@[simp]
lemma prod_id {X Y : C} : 𝟙 X π 𝟙 Y = 𝟙 (X π Y) :=
by simp [prod_hom_def]

end cartesian_category

namespace cocartesian_category
variables [cocartesian_category.{v} C]
infixr ` ⨿ `:70          := coprod_obj
infixr ` ⨿ `:70          := coprod_hom

variables {X₁ X₂ Y₁ Y₂ Z W : C}

lemma coprod_hom_def (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  coprod_hom f g = coprod_elim (f ≫ coprod_intro_left _ _) (g ≫ coprod_intro_right _ _) :=
begin
  rw [← intro_left_hom C f g,← intro_right_hom _ f g,coprod_elim_comp],
end

@[extensionality]
lemma ext (f g : X₁ ⨿ X₂ ⟶ Z)
  (h₀ : coprod_intro_left X₁ X₂ ≫ f = coprod_intro_left X₁ X₂ ≫ g)
  (h₁ : coprod_intro_right X₁ X₂ ≫ f = coprod_intro_right X₁ X₂ ≫ g) :
  f = g :=
begin
  transitivity coprod_elim (coprod_intro_left X₁ X₂ ≫ f) (coprod_intro_right X₁ X₂ ≫ f),
  rw coprod_elim_comp,
  rw [h₀,h₁,coprod_elim_comp],
end

lemma coprod_elim_comp' (f : X₁ ⟶ Z) (g : X₂ ⟶ Z) (h : Z ⟶ W) : coprod_elim (f ≫ h) (g ≫ h) = coprod_elim f g ≫ h :=
ext _ _
  (by rw [coprod_intro_left_elim,← category.assoc,coprod_intro_left_elim])
  (by rw [coprod_intro_right_elim,← category.assoc,coprod_intro_right_elim])

@[simp]
lemma elim_unique' (f f' : zero C ⟶ Z) : f = f' ↔ true := by simp [elim_unique _ _ f,elim_unique _ _ f']

end cocartesian_category

@[simp]
lemma unop_intro (X Y : Cᵒᵖ) (f g : X ⟶ Y) : f = g ↔ f.unop = g.unop :=
⟨ λ h, h ▸ rfl, λ h, has_hom.hom.unop_inj h ⟩

namespace cartesian_category
variables [𝒟 : cartesian_category.{v} C]
include 𝒟

open opposite has_hom.hom

def left_unitor (X : C) : one C π X ≅ X :=
{ hom := prod_elim_right _ _,
  inv := prod_intro (intro _) (𝟙 _)   }

def right_unitor (X : C) : X π one C ≅ X :=
{ hom := prod_elim_left _ _,
  inv := prod_intro (𝟙 _) (intro _)   }

def associator (X Y Z : C) : (X π Y) π Z ≅ X π Y π Z :=
{ hom := prod_intro (prod_elim_left _ _ ≫ prod_elim_left _ _)
                    (prod_intro (prod_elim_left _ _ ≫ prod_elim_right _ _)
                                (prod_elim_right _ _)),
  inv := prod_intro (prod_intro (prod_elim_left _ _)
                                (prod_elim_right _ _ ≫ prod_elim_left _ _))
                    (prod_elim_right _ _ ≫ prod_elim_right _ _) }

local attribute [simp] associator left_unitor right_unitor

instance monoidal_category.of_cartesian_category : monoidal_category C :=
{ tensor_obj := prod_obj,
  tensor_hom := @prod_hom C _ _,
  tensor_unit := one C,
  left_unitor := left_unitor,
  right_unitor := right_unitor,
  associator := associator }

instance : cocartesian_category (Cᵒᵖ) :=
{ coprod_obj := λ X Y, op $ prod_obj (unop X) (unop Y),
  zero := op $ one C,
  coprod_hom := λ X₁ Y₁ X₂ Y₂ f g, (f.unop π g.unop).op,
  coprod_intro_left := λ Y₁ Y₂, (prod_elim_left (unop Y₁) (unop Y₂)).op,
  coprod_intro_right := λ Y₁ Y₂, (prod_elim_right (unop Y₁) (unop Y₂)).op,
  coprod_elim := λ X₁ X₂ Y f g, (prod_intro f.unop g.unop).op,
  elim := λ X, (intro $ unop X).op,
 }

omit 𝒞 𝒟

instance : cartesian_category (Type*) :=
{ one := punit,
  prod_obj := prod,
  prod_hom := @prod.map,
  intro := λ X a, punit.star,
  prod_intro := λ X Y₁ Y₂ f g x, (f x, g x),
  prod_elim_left := λ Y₁ Y₂, @_root_.prod.fst Y₁ Y₂,
  prod_elim_right := λ Y₁ Y₂, @_root_.prod.snd Y₁ Y₂ }

end cartesian_category

namespace cocartesian_category

variables [𝒟 : cocartesian_category.{v} C]
include 𝒟

instance : cartesian_category (Cᵒᵖ) :=
{ one := op $ zero C,
  prod_obj := λ X Y, op (coprod_obj (unop X) (unop Y)),
  prod_hom := λ X₁ Y₁ X₂ Y₂ f g, (coprod_hom f.unop g.unop).op,
  intro := λ X, (elim (unop X)).op,
  prod_intro := λ X Y₁ Y₂ f g, (coprod_elim f.unop g.unop).op,
  prod_elim_right := λ Y₁ Y₂, (coprod_intro_right (unop Y₁) (unop Y₂)).op,
  prod_elim_left :=  λ Y₁ Y₂, (coprod_intro_left (unop Y₁) (unop Y₂)).op }

open opposite has_hom.hom

omit 𝒞 𝒟

instance : cocartesian_category Type* :=
{ zero := pempty,
  coprod_obj := sum,
  coprod_hom := @sum.map,
  elim := λ X a, a.elim,
  coprod_elim := λ X Y Z f g a, sum.cases_on a f g,
  coprod_intro_left := @sum.inl,
  coprod_intro_right := @sum.inr }

end cocartesian_category

end category_theory
