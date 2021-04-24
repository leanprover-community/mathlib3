/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.monoidal.category
import category_theory.groupoid

universes v u

namespace category_theory
open monoidal_category

variables {C : Type u}

section
variables (C)

inductive free_monoidal_category : Type u
| of : C → free_monoidal_category
| unit : free_monoidal_category
| tensor : free_monoidal_category → free_monoidal_category → free_monoidal_category

end

local notation `F` := free_monoidal_category

namespace free_monoidal_category

inductive hom : F C → F C → Type u
| id (X) : hom X X
| α_hom (X Y Z : F C) : hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
| α_inv (X Y Z : F C) : hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
| l_hom (X) : hom (unit.tensor X) X
| l_inv (X) : hom X (unit.tensor X)
| ρ_hom (X : F C) : hom (X.tensor unit) X
| ρ_inv (X : F C) : hom X (X.tensor unit)
| comp {X Y Z} (f : hom X Y) (g : hom Y Z) : hom X Z
| tensor {W X Y Z} (f : hom W Y) (g : hom X Z) : hom (W.tensor X) (Y.tensor Z)

infixr ` ⟶ᵐ `:10 := hom

inductive hom_equiv : Π (X Y : F C), (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
| refl {X Y} (f) : hom_equiv X Y f f
| symm {X Y} (f g) : hom_equiv X Y f g → hom_equiv X Y g f
| trans {X Y} {f g h} : hom_equiv X Y f g → hom_equiv X Y g h → hom_equiv X Y f h
| comp {X Y Z : F C} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
    hom_equiv X Y f f' → hom_equiv Y Z g g' → hom_equiv X Z (f.comp g) (f'.comp g')
| tensor {W X Y Z : F C} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
    hom_equiv _ _ f f' → hom_equiv _ _ g g' → hom_equiv _ _ (f.tensor g) (f'.tensor g')
| comp_id {X Y} (f : X ⟶ᵐ Y) : hom_equiv X Y (f.comp (hom.id _)) f
| id_comp {X Y} (f : X ⟶ᵐ Y) : hom_equiv X Y ((hom.id _).comp f) f
| assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
    hom_equiv X Y ((f.comp g).comp h) (f.comp (g.comp h))
| tensor_id {X Y : F C} : hom_equiv _ _ ((hom.id X).tensor (hom.id Y)) (hom.id _)
| tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    hom_equiv _ _ ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
| α_hom_inv {X Y Z : F C} : hom_equiv _ _ ((hom.α_hom X Y Z).comp (hom.α_inv X Y Z)) (hom.id _)
| α_inv_hom {X Y Z : F C} : hom_equiv _ _ ((hom.α_inv X Y Z).comp (hom.α_hom X Y Z)) (hom.id _)
| associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
    hom_equiv _ _ (((f₁.tensor f₂).tensor f₃).comp (hom.α_hom Y₁ Y₂ Y₃))
      ((hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
| ρ_hom_inv {X : F C} : hom_equiv _ _ ((hom.ρ_hom X).comp (hom.ρ_inv X)) (hom.id _)
| ρ_inv_hom {X : F C} : hom_equiv _ _ ((hom.ρ_inv X).comp (hom.ρ_hom X)) (hom.id _)
| ρ_naturality {X Y : F C} (f : X ⟶ᵐ Y) : hom_equiv _ _
    ((f.tensor (hom.id unit)).comp (hom.ρ_hom Y)) ((hom.ρ_hom X).comp f)
| l_hom_inv {X : F C} : hom_equiv _ _ ((hom.l_hom X).comp (hom.l_inv X)) (hom.id _)
| l_inv_hom {X : F C} : hom_equiv _ _ ((hom.l_inv X).comp (hom.l_hom X)) (hom.id _)
| l_naturality {X Y : F C} (f : X ⟶ᵐ Y) : hom_equiv _ _
    (((hom.id unit).tensor f).comp (hom.l_hom Y)) ((hom.l_hom X).comp f)
| pentagon {W X Y Z : F C} : hom_equiv _ _
  (((hom.α_hom W X Y).tensor (hom.id Z)).comp
    ((hom.α_hom W (X.tensor Y) Z).comp ((hom.id W).tensor (hom.α_hom X Y Z))))
  ((hom.α_hom (W.tensor X) Y Z).comp (hom.α_hom W X (Y.tensor Z)))
| triangle {X Y : F C} : hom_equiv _ _ ((hom.α_hom X unit Y).comp ((hom.id X).tensor (hom.l_hom Y)))
  ((hom.ρ_hom X).tensor (hom.id Y))

def setoid_hom (X Y : F C) : setoid (X ⟶ᵐ Y) :=
⟨hom_equiv X Y,
  ⟨λ f, hom_equiv.refl f, λ f g, hom_equiv.symm f g, λ f g h hfg hgh, hom_equiv.trans hfg hgh⟩⟩

attribute [instance] setoid_hom

section
open free_monoidal_category.hom_equiv

instance category_free_monoidal_category : category.{u} (F C) :=
{ hom := λ X Y, quotient (free_monoidal_category.setoid_hom X Y),
  id := λ X, ⟦free_monoidal_category.hom.id _⟧,
  comp := λ X Y Z f g, quotient.map₂ hom.comp (by { intros f f' hf g g' hg, exact comp hf hg }) f g,
  id_comp' := by { rintro X Y ⟨f⟩, exact quotient.sound (id_comp f) },
  comp_id' := by { rintro X Y ⟨f⟩, exact quotient.sound (comp_id f) },
  assoc' := by { rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩, exact quotient.sound (assoc f g h) } }

instance : monoidal_category (F C) :=
{ tensor_obj := λ X Y, free_monoidal_category.tensor X Y,
  tensor_hom := λ X₁ Y₁ X₂ Y₂, quotient.map₂ hom.tensor $
    by { intros _ _ h _ _ h', exact hom_equiv.tensor h h'},
  tensor_id' := λ X Y, quotient.sound tensor_id,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂,
    by { rintros ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩, exact quotient.sound (tensor_comp _ _ _ _) },
  tensor_unit := free_monoidal_category.unit,
  associator := λ X Y Z,
    ⟨⟦hom.α_hom X Y Z⟧, ⟦hom.α_inv X Y Z⟧, quotient.sound α_hom_inv, quotient.sound α_inv_hom⟩,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃,
    by { rintros ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩, exact quotient.sound (associator_naturality _ _ _) },
  left_unitor := λ X,
   ⟨⟦hom.l_hom X⟧, ⟦hom.l_inv X⟧, quotient.sound l_hom_inv, quotient.sound l_inv_hom⟩,
  left_unitor_naturality' := λ X Y, by { rintro ⟨f⟩, exact quotient.sound (l_naturality _) },
  right_unitor := λ X,
   ⟨⟦hom.ρ_hom X⟧, ⟦hom.ρ_inv X⟧, quotient.sound ρ_hom_inv, quotient.sound ρ_inv_hom⟩,
  right_unitor_naturality' := λ X Y, by { rintro ⟨f⟩, exact quotient.sound (ρ_naturality _) },
  pentagon' := λ W X Y Z, quotient.sound pentagon,
  triangle' := λ X Y, quotient.sound triangle }

@[simp] lemma mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
  ⟦f.comp g⟧ = @category_struct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
rfl

@[simp] lemma mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
  ⟦f.tensor g⟧ = @monoidal_category.tensor_hom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
rfl

@[simp] lemma mk_id {X : F C} : ⟦hom.id X⟧ = 𝟙 X := rfl
@[simp] lemma mk_α_hom {X Y Z : F C} : ⟦hom.α_hom X Y Z⟧ = (α_ X Y Z).hom := rfl
@[simp] lemma mk_α_inv {X Y Z : F C} : ⟦hom.α_inv X Y Z⟧ = (α_ X Y Z).inv := rfl
@[simp] lemma mk_ρ_hom {X : F C} : ⟦hom.ρ_hom X⟧ = (ρ_ X).hom := rfl
@[simp] lemma mk_ρ_inv {X : F C} : ⟦hom.ρ_inv X⟧ = (ρ_ X).inv := rfl
@[simp] lemma mk_l_hom {X : F C} : ⟦hom.l_hom X⟧ = (λ_ X).hom := rfl
@[simp] lemma mk_l_inv {X : F C} : ⟦hom.l_inv X⟧ = (λ_ X).inv := rfl
@[simp] lemma tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y := rfl
@[simp] lemma unit_eq_unit : free_monoidal_category.unit = 𝟙_ (F C) := rfl

section
open hom

@[simp] def inverse' : Π {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
| _ _ (id X) := id X
| _ _ (α_hom _ _ _) := α_inv _ _ _
| _ _ (α_inv _ _ _) := α_hom _ _ _
| _ _ (ρ_hom _) := ρ_inv _
| _ _ (ρ_inv _) := ρ_hom _
| _ _ (l_hom _) := l_inv _
| _ _ (l_inv _) := l_hom _
| _ _ (comp f g) := (inverse' g).comp (inverse' f)
| _ _ (hom.tensor f g) := (inverse' f).tensor (inverse' g)

end

def inverse {X Y : F C} : (X ⟶ Y) → (Y ⟶ X) :=
quotient.lift (λ f, ⟦inverse' f⟧)
begin
  intros f g h,
  dsimp only,
  induction h with X f f X Y f h hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg
    X₁ Y₁ X₂ Y₂ f f' g g' _ _ hf hg,
  { refl },
  { exact hfg'.symm },
  { exact hfg.trans hgh },
  { simp only [inverse', mk_comp, hf, hg] },
  { simp only [inverse', mk_tensor, hf, hg] },
  all_goals { simp only [inverse', mk_id, mk_comp, mk_α_hom, mk_α_inv, mk_ρ_hom, mk_ρ_inv, mk_l_hom,
    mk_l_inv, category.id_comp, category.comp_id, category.assoc, iso.hom_inv_id, iso.inv_hom_id,
      mk_tensor, monoidal_category.tensor_id, monoidal_category.tensor_comp],
    try { dsimp only [tensor_eq_tensor, unit_eq_unit],
      simp only [eq_self_iff_true, associator_inv_naturality, right_unitor_inv_naturality,
        left_unitor_inv_naturality, pentagon_inv, triangle_assoc_comp_left_inv] } }
end


section functor
variables [category.{v} C] [monoidal_category C]

def project_obj : F C → C
| (free_monoidal_category.of X) := X
| free_monoidal_category.unit := 𝟙_ C
| (free_monoidal_category.tensor X Y) := project_obj X ⊗ project_obj Y

section
open hom

@[simp]
def project_hom' : Π {X Y : F C}, (X ⟶ᵐ Y) → (project_obj X ⟶ project_obj Y)
| _ _ (id _) := 𝟙 _
| _ _ (α_hom _ _ _) := (α_ _ _ _).hom
| _ _ (α_inv _ _ _) := (α_ _ _ _).inv
| _ _ (l_hom _) := (λ_ _).hom
| _ _ (l_inv _) := (λ_ _).inv
| _ _ (ρ_hom _) := (ρ_ _).hom
| _ _ (ρ_inv _) := (ρ_ _).inv
| _ _ (comp f g) := project_hom' f ≫ project_hom' g
| _ _ (hom.tensor f g) := project_hom' f ⊗ project_hom' g

def project_hom {X Y : F C} : (X ⟶ Y) → (project_obj X ⟶ project_obj Y) :=
quotient.lift project_hom'
begin
  intros f g h,
  induction h with X Y f X Y f g hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg
    W X Y Z f g f' g' _ _ hfg hfg',
  { refl },
  { exact hfg'.symm },
  { exact hfg.trans hgh },
  { simp only [project_hom', hf, hg] },
  { simp only [project_hom', hfg, hfg'] },
  { simp only [project_hom', category.comp_id] },
  { simp only [project_hom', category.id_comp] },
  { simp only [project_hom', category.assoc ] },
  { simp only [project_hom', monoidal_category.tensor_id], refl },
  { simp only [project_hom', monoidal_category.tensor_comp] },
  { simp only [project_hom', iso.hom_inv_id] },
  { simp only [project_hom', iso.inv_hom_id] },
  { simp only [project_hom', monoidal_category.associator_naturality] },
  { simp only [project_hom', iso.hom_inv_id] },
  { simp only [project_hom', iso.inv_hom_id] },
  { simp only [project_hom'], dsimp [project_obj],
    exact monoidal_category.right_unitor_naturality _ },
  { simp only [project_hom', iso.hom_inv_id] },
  { simp only [project_hom', iso.inv_hom_id] },
  { simp only [project_hom'], dsimp [project_obj],
    exact monoidal_category.left_unitor_naturality _ },
  { simp only [project_hom'], exact monoidal_category.pentagon _ _ _ _ },
  { simp only [project_hom'], exact monoidal_category.triangle _ _ }
end

end

def project : F C ⥤ C :=
{ obj := project_obj,
  map := λ X Y, project_hom }

end functor

end

end free_monoidal_category

end category_theory
