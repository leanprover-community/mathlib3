/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.monoidal.category
import category_theory.groupoid

universes v u

namespace category_theory

variables {C : Type u}

section
variables (C)

inductive free_monoidal_category : Type u
| of : C → free_monoidal_category
| unit : free_monoidal_category
| tensor : free_monoidal_category → free_monoidal_category → free_monoidal_category

end

notation `F` := free_monoidal_category

inductive free_monoidal_category_hom : F C → F C → Type u
| id (X) : free_monoidal_category_hom X X
| α_hom (X Y Z : F C) : free_monoidal_category_hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
| α_inv (X Y Z) : free_monoidal_category_hom (free_monoidal_category.tensor X (free_monoidal_category.tensor Y Z)) (free_monoidal_category.tensor (free_monoidal_category.tensor X Y) Z)
| l_hom (X) : free_monoidal_category_hom (free_monoidal_category.tensor free_monoidal_category.unit X) X
| l_inv (X) : free_monoidal_category_hom X (free_monoidal_category.tensor free_monoidal_category.unit X)
| ρ_hom (X) : free_monoidal_category_hom (free_monoidal_category.tensor X free_monoidal_category.unit) X
| ρ_inv (X) : free_monoidal_category_hom X (free_monoidal_category.tensor X free_monoidal_category.unit)
| comp {X Y Z} (f : free_monoidal_category_hom X Y) (g : free_monoidal_category_hom Y Z) : free_monoidal_category_hom X Z
| tensor {W X Y Z} (f : free_monoidal_category_hom W Y) (g : free_monoidal_category_hom X Z) : free_monoidal_category_hom (free_monoidal_category.tensor W X) (free_monoidal_category.tensor Y Z)

infixr ` ⟶ᵐ `:10 := free_monoidal_category_hom

inductive free_monoidal_category_hom_equiv : Π (X Y : F C), free_monoidal_category_hom X Y → free_monoidal_category_hom X Y → Prop
| refl {X Y} (f) : free_monoidal_category_hom_equiv X Y f f
| symm {X Y} (f g) : free_monoidal_category_hom_equiv X Y f g → free_monoidal_category_hom_equiv X Y g f
| trans {X Y} {f g h} : free_monoidal_category_hom_equiv X Y f g → free_monoidal_category_hom_equiv X Y g h → free_monoidal_category_hom_equiv X Y f h
| comp {X Y Z : F C} {f f' : free_monoidal_category_hom X Y} {g g' : free_monoidal_category_hom Y Z} : free_monoidal_category_hom_equiv X Y f f' → free_monoidal_category_hom_equiv Y Z g g' → free_monoidal_category_hom_equiv X Z (f.comp g) (f'.comp g')
| tensor {W X Y Z : F C} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} : free_monoidal_category_hom_equiv _ _ f f' → free_monoidal_category_hom_equiv _ _ g g' → free_monoidal_category_hom_equiv _ _ (f.tensor g) (f'.tensor g')
| comp_id {X Y} (f : free_monoidal_category_hom X Y) : free_monoidal_category_hom_equiv X Y (f.comp (free_monoidal_category_hom.id _)) f
| id_comp {X Y} (f : free_monoidal_category_hom X Y) : free_monoidal_category_hom_equiv X Y ((free_monoidal_category_hom.id _).comp f) f
| assoc {X Y U V : F C} (f : free_monoidal_category_hom X U) (g : free_monoidal_category_hom U V) (h : free_monoidal_category_hom V Y) :
    free_monoidal_category_hom_equiv X Y ((f.comp g).comp h) (f.comp (g.comp h))
| tensor_id {X Y : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.id X).tensor (free_monoidal_category_hom.id Y)) (free_monoidal_category_hom.id _)
| tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    free_monoidal_category_hom_equiv _ _ ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
| α_hom_inv {X Y Z : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.α_hom X Y Z).comp (free_monoidal_category_hom.α_inv X Y Z)) (free_monoidal_category_hom.id _)
| α_inv_hom {X Y Z : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.α_inv X Y Z).comp (free_monoidal_category_hom.α_hom X Y Z)) (free_monoidal_category_hom.id _)
| associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
    free_monoidal_category_hom_equiv _ _ (((f₁.tensor f₂).tensor f₃).comp (free_monoidal_category_hom.α_hom Y₁ Y₂ Y₃))
      ((free_monoidal_category_hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
| ρ_hom_inv {X : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.ρ_hom X).comp (free_monoidal_category_hom.ρ_inv X)) (free_monoidal_category_hom.id _)
| ρ_inv_hom {X : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.ρ_inv X).comp (free_monoidal_category_hom.ρ_hom X)) (free_monoidal_category_hom.id _)
| ρ_naturality {X Y : F C} (f : X ⟶ᵐ Y) : free_monoidal_category_hom_equiv _ _ ((f.tensor (free_monoidal_category_hom.id free_monoidal_category.unit)).comp (free_monoidal_category_hom.ρ_hom Y)) ((free_monoidal_category_hom.ρ_hom X).comp f)
| l_hom_inv {X : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.l_hom X).comp (free_monoidal_category_hom.l_inv X)) (free_monoidal_category_hom.id _)
| l_inv_hom {X : F C} : free_monoidal_category_hom_equiv _ _ ((free_monoidal_category_hom.l_inv X).comp (free_monoidal_category_hom.l_hom X)) (free_monoidal_category_hom.id _)
| l_naturality {X Y : F C} (f : X ⟶ᵐ Y) : free_monoidal_category_hom_equiv _ _ (((free_monoidal_category_hom.id free_monoidal_category.unit).tensor f).comp (free_monoidal_category_hom.l_hom Y)) ((free_monoidal_category_hom.l_hom X).comp f)
| pentagon {W X Y Z : F C} : free_monoidal_category_hom_equiv _ _
    (((free_monoidal_category_hom.α_hom W X Y).tensor (free_monoidal_category_hom.id Z)).comp
      ((free_monoidal_category_hom.α_hom W (X.tensor Y) Z).comp ((free_monoidal_category_hom.id W).tensor (free_monoidal_category_hom.α_hom X Y Z))))
    ((free_monoidal_category_hom.α_hom (W.tensor X) Y Z).comp (free_monoidal_category_hom.α_hom W X (Y.tensor Z)))
| triangle {X Y : F C} : free_monoidal_category_hom_equiv _ _
  ((free_monoidal_category_hom.α_hom X free_monoidal_category.unit Y).comp ((free_monoidal_category_hom.id X).tensor (free_monoidal_category_hom.l_hom Y)))
  ((free_monoidal_category_hom.ρ_hom X).tensor (free_monoidal_category_hom.id Y))

def setoid_free_monoidal_category_hom (X Y : F C) : setoid (free_monoidal_category_hom X Y) :=
⟨free_monoidal_category_hom_equiv X Y,
  ⟨λ f, free_monoidal_category_hom_equiv.refl f,
   λ f g, free_monoidal_category_hom_equiv.symm f g,
   λ f g h hfg hgh, free_monoidal_category_hom_equiv.trans hfg hgh⟩⟩

attribute [instance] setoid_free_monoidal_category_hom

section
open free_monoidal_category_hom_equiv

end

instance category_free_monoidal_category : category.{u} (F C) :=
{ hom := λ X Y, quotient (setoid_free_monoidal_category_hom X Y),
  id := λ X, ⟦free_monoidal_category_hom.id _⟧,
  comp := λ X Y Z f g, quotient.map₂ free_monoidal_category_hom.comp (--λ f f' hf g g' hg,
    begin
      intros f f' hf g g' hg,
      exact free_monoidal_category_hom_equiv.comp hf hg
    end) f g,
  id_comp' := λ X Y f, --quotient.induction_on f $ quotient.sound (free_monoidal_category_hom_equiv.id_comp f),
  begin
    induction f,
    { apply quotient.sound,
      exact free_monoidal_category_hom_equiv.id_comp f },
    { refl }
  end,
  comp_id' := λ X Y f,
  begin
    induction f,
    { apply quotient.sound,
      exact free_monoidal_category_hom_equiv.comp_id f },
    { refl }
  end,
  assoc' := λ W X Y Z f g h,
  begin
    induction f,
    { induction g,
      { induction h,
        { apply quotient.sound,
          exact free_monoidal_category_hom_equiv.assoc f g h },
        { refl } },
      { refl } },
    { refl }
  end }

instance : monoidal_category (F C) :=
{ tensor_obj := λ X Y, free_monoidal_category.tensor X Y,
  tensor_hom := λ X₁ Y₁ X₂ Y₂, quotient.map₂ free_monoidal_category_hom.tensor
  begin
    intros f f' hf g g' hg,
    exact free_monoidal_category_hom_equiv.tensor hf hg
  end,
  tensor_id' := λ X Y,
  begin
    apply quotient.sound,
    exact free_monoidal_category_hom_equiv.tensor_id
  end,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂,
  begin
    rintros ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩,
    exact quotient.sound (free_monoidal_category_hom_equiv.tensor_comp _ _ _ _)
  end,
  tensor_unit := free_monoidal_category.unit,
  associator := λ X Y Z,
  { hom := ⟦free_monoidal_category_hom.α_hom X Y Z⟧,
    inv := ⟦free_monoidal_category_hom.α_inv X Y Z⟧,
    hom_inv_id' := quotient.sound free_monoidal_category_hom_equiv.α_hom_inv,
    inv_hom_id' := quotient.sound free_monoidal_category_hom_equiv.α_inv_hom },
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃,
  begin
    rintros ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩,
    exact quotient.sound (free_monoidal_category_hom_equiv.associator_naturality _ _ _)
  end,
  left_unitor := λ X,
  { hom := ⟦free_monoidal_category_hom.l_hom X⟧,
    inv := ⟦free_monoidal_category_hom.l_inv X⟧,
    hom_inv_id' := quotient.sound free_monoidal_category_hom_equiv.l_hom_inv,
    inv_hom_id' := quotient.sound free_monoidal_category_hom_equiv.l_inv_hom },
  left_unitor_naturality' := λ X Y,
  begin
    rintro ⟨f⟩,
    exact quotient.sound (free_monoidal_category_hom_equiv.l_naturality _)
  end,
  right_unitor := λ X,
  { hom := ⟦free_monoidal_category_hom.ρ_hom X⟧,
    inv := ⟦free_monoidal_category_hom.ρ_inv X⟧,
    hom_inv_id' := quotient.sound free_monoidal_category_hom_equiv.ρ_hom_inv,
    inv_hom_id' := quotient.sound free_monoidal_category_hom_equiv.ρ_inv_hom },
  right_unitor_naturality' := λ X Y,
  begin
    rintro ⟨f⟩,
    exact quotient.sound (free_monoidal_category_hom_equiv.ρ_naturality _)
  end,
  pentagon' := λ W X Y Z, quotient.sound free_monoidal_category_hom_equiv.pentagon,
  triangle' := λ X Y, quotient.sound free_monoidal_category_hom_equiv.triangle }

--instance {X Y : F C} (f : X ⟶ Y) : is_iso f :=

section
open free_monoidal_category_hom

@[simp] def inverse' : Π {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
| _ _ (id X) := id X
| _ _ (α_hom _ _ _) := α_inv _ _ _
| _ _ (α_inv _ _ _) := α_hom _ _ _
| _ _ (ρ_hom _) := ρ_inv _
| _ _ (ρ_inv _) := ρ_hom _
| _ _ (l_hom _) := l_inv _
| _ _ (l_inv _) := l_hom _
| _ _ (comp f g) := (inverse' g).comp (inverse' f)
| _ _ (tensor f g) := (inverse' f).tensor (inverse' g)

end

@[simp] lemma mk_comp_eq_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
  ⟦f.comp g⟧ = @category_struct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
rfl

@[simp] lemma mk_tensor_eq_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
  ⟦f.tensor g⟧ = @monoidal_category.tensor_hom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
rfl

@[simp] lemma mk_id_eq_id {X : F C} : ⟦free_monoidal_category_hom.id X⟧ = 𝟙 X :=
rfl

@[simp] lemma tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
rfl

@[simp] lemma mk_α_hom {X Y Z : F C} : ⟦free_monoidal_category_hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
rfl

@[simp] lemma mk_α_inv {X Y Z : F C} : ⟦free_monoidal_category_hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
rfl

@[simp] lemma mk_ρ_hom {X : F C} : ⟦free_monoidal_category_hom.ρ_hom X⟧ = (ρ_ X).hom :=
rfl

@[simp] lemma mk_ρ_inv {X : F C} : ⟦free_monoidal_category_hom.ρ_inv X⟧ = (ρ_ X).inv :=
rfl

@[simp] lemma mk_l_hom {X : F C} : ⟦free_monoidal_category_hom.l_hom X⟧ = (λ_ X).hom :=
rfl

@[simp] lemma mk_l_inv {X : F C} : ⟦free_monoidal_category_hom.l_inv X⟧ = (λ_ X).inv :=
rfl

@[simp] lemma unit_eq_unit : free_monoidal_category.unit = 𝟙_ (F C) :=
rfl

@[simp] def inverse {X Y : F C} : (X ⟶ Y) → (Y ⟶ X) :=
quotient.lift (λ f, ⟦inverse' f⟧)
begin
  intros f g h,
  dsimp,
  induction h with X f f X Y f h hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg
    X₁ Y₁ X₂ Y₂ f f' g g' _ _ hf hg
    X Y f X Y f X Y U V f g h X Y X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂ X Y Z X Y Z X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃,
  { refl },
  { exact hfg'.symm },
  { exact hfg.trans hgh },
  { simp only [inverse', mk_comp_eq_comp, hf, hg] },
  { simp only [inverse', mk_tensor_eq_tensor, hf, hg] },
  { simp only [inverse', mk_comp_eq_comp, mk_id_eq_id, category.id_comp] },
  { simp only [inverse', mk_comp_eq_comp, mk_id_eq_id, category.comp_id] },
  { simp only [inverse', mk_comp_eq_comp, category.assoc] },
  { simp only [inverse', mk_tensor_eq_tensor, mk_id_eq_id, monoidal_category.tensor_id], refl },
  { simp only [inverse', mk_comp_eq_comp, monoidal_category.tensor_comp, mk_tensor_eq_tensor] },
  { simp only [inverse', iso.hom_inv_id, mk_comp_eq_comp, mk_α_inv, mk_id_eq_id, mk_α_hom], },
  { simp only [inverse', mk_comp_eq_comp, mk_α_inv, mk_id_eq_id, mk_α_hom, iso.inv_hom_id], },
  { simp only [inverse', mk_comp_eq_comp, mk_α_inv, mk_tensor_eq_tensor, monoidal_category.associator_inv_naturality] },
  { simp only [inverse', iso.hom_inv_id, mk_comp_eq_comp, mk_id_eq_id, mk_ρ_hom, mk_ρ_inv], },
  { simp only [inverse', mk_comp_eq_comp, mk_id_eq_id, mk_ρ_hom, mk_ρ_inv, iso.inv_hom_id], },
  { simp only [inverse', mk_comp_eq_comp, mk_id_eq_id, mk_tensor_eq_tensor, mk_ρ_inv, monoidal_category.right_unitor_inv_naturality], refl },
  { simp only [inverse', iso.hom_inv_id, mk_l_inv, mk_comp_eq_comp, mk_id_eq_id, mk_l_hom] },
  { simp only [inverse', mk_l_inv, mk_comp_eq_comp, mk_id_eq_id, mk_l_hom, iso.inv_hom_id] },
  { simp only [inverse', mk_l_inv, mk_comp_eq_comp, mk_id_eq_id, mk_tensor_eq_tensor, monoidal_category.left_unitor_inv_naturality], refl },
  { simp only [inverse', mk_comp_eq_comp, mk_α_inv, mk_id_eq_id, mk_tensor_eq_tensor, category.assoc], exact monoidal_category.pentagon_inv _ _ _ _ },
  { simp only [inverse', mk_l_inv, mk_comp_eq_comp, mk_α_inv, mk_id_eq_id, mk_tensor_eq_tensor, mk_ρ_inv], exact monoidal_category.triangle_assoc_comp_left_inv _ _ }
end


section functor
variables [category.{v} C] [monoidal_category C]

def project_obj : F C → C
| (free_monoidal_category.of X) := X
| free_monoidal_category.unit := 𝟙_ C
| (free_monoidal_category.tensor X Y) := project_obj X ⊗ project_obj Y

section
open free_monoidal_category_hom

def project_hom' : Π {X Y : F C}, free_monoidal_category_hom X Y → (project_obj X ⟶ project_obj Y)
| _ _ (id _) := 𝟙 _
| _ _ (α_hom _ _ _) := (α_ _ _ _).hom
| _ _ (α_inv _ _ _) := (α_ _ _ _).inv
| _ _ (l_hom _) := (λ_ _).hom
| _ _ (l_inv _) := (λ_ _).inv
| _ _ (ρ_hom _) := (ρ_ _).hom
| _ _ (ρ_inv _) := (ρ_ _).inv
| _ _ (comp f g) := project_hom' f ≫ project_hom' g
| _ _ (tensor f g) := project_hom' f ⊗ project_hom' g

def project_hom {X Y : F C} : (X ⟶ Y) → (project_obj X ⟶ project_obj Y) :=
quotient.lift project_hom'
begin
  intros f g h,
  induction h with X Y f X Y f g hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg W X Y Z f g f' g' _ _ hfg hfg' X Y f X Y f,
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
  { simp only [project_hom'], dsimp [project_obj], exact monoidal_category.right_unitor_naturality _ },
  { simp only [project_hom', iso.hom_inv_id] },
  { simp only [project_hom', iso.inv_hom_id] },
  { simp only [project_hom'], dsimp [project_obj], exact monoidal_category.left_unitor_naturality _ },
  { simp only [project_hom'], exact monoidal_category.pentagon _ _ _ _ },
  { simp only [project_hom'], exact monoidal_category.triangle _ _ }
end

end

def project : F C ⥤ C :=
{ obj := project_obj,
  map := λ X Y, project_hom }

end functor

end category_theory
