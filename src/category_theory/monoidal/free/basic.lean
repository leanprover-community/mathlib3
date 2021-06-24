/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.monoidal.functor
import category_theory.groupoid

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `free_monoidal_category C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `coherence.lean`.

-/

universes v' u u'

namespace category_theory
open monoidal_category

variables {C : Type u}

section
variables (C)

/--
Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.
-/
@[derive inhabited]
inductive free_monoidal_category : Type u
| of : C → free_monoidal_category
| unit : free_monoidal_category
| tensor : free_monoidal_category → free_monoidal_category → free_monoidal_category

end

local notation `F` := free_monoidal_category

namespace free_monoidal_category

/-- Formal compositions and tensor products of identities, unitors and associators. The morphisms
    of the free monoidal category are obtained as a quotient of these formal morphisms by the
    relations defining a monoidal category. -/
@[nolint has_inhabited_instance]
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

local infixr ` ⟶ᵐ `:10 := hom

/-- The morphisms of the free monoidal category satisfy 21 relations ensuring that the resulting
    category is in fact a category and that it is monoidal. -/
inductive hom_equiv : Π {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
| refl {X Y} (f : X ⟶ᵐ Y) : hom_equiv f f
| symm {X Y} (f g : X ⟶ᵐ Y) : hom_equiv f g → hom_equiv g f
| trans {X Y} {f g h : X ⟶ᵐ Y} : hom_equiv f g → hom_equiv g h → hom_equiv f h
| comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f.comp g) (f'.comp g')
| tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f.tensor g) (f'.tensor g')
| comp_id {X Y} (f : X ⟶ᵐ Y) : hom_equiv (f.comp (hom.id _)) f
| id_comp {X Y} (f : X ⟶ᵐ Y) : hom_equiv ((hom.id _).comp f) f
| assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
    hom_equiv ((f.comp g).comp h) (f.comp (g.comp h))
| tensor_id {X Y} : hom_equiv ((hom.id X).tensor (hom.id Y)) (hom.id _)
| tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C}
    (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    hom_equiv ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
| α_hom_inv {X Y Z} : hom_equiv ((hom.α_hom X Y Z).comp (hom.α_inv X Y Z)) (hom.id _)
| α_inv_hom {X Y Z} : hom_equiv ((hom.α_inv X Y Z).comp (hom.α_hom X Y Z)) (hom.id _)
| associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
    hom_equiv (((f₁.tensor f₂).tensor f₃).comp (hom.α_hom Y₁ Y₂ Y₃))
      ((hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
| ρ_hom_inv {X} : hom_equiv ((hom.ρ_hom X).comp (hom.ρ_inv X)) (hom.id _)
| ρ_inv_hom {X} : hom_equiv ((hom.ρ_inv X).comp (hom.ρ_hom X)) (hom.id _)
| ρ_naturality {X Y} (f : X ⟶ᵐ Y) : hom_equiv
    ((f.tensor (hom.id unit)).comp (hom.ρ_hom Y)) ((hom.ρ_hom X).comp f)
| l_hom_inv {X} : hom_equiv ((hom.l_hom X).comp (hom.l_inv X)) (hom.id _)
| l_inv_hom {X} : hom_equiv ((hom.l_inv X).comp (hom.l_hom X)) (hom.id _)
| l_naturality {X Y} (f : X ⟶ᵐ Y) : hom_equiv
    (((hom.id unit).tensor f).comp (hom.l_hom Y)) ((hom.l_hom X).comp f)
| pentagon {W X Y Z} : hom_equiv
  (((hom.α_hom W X Y).tensor (hom.id Z)).comp
    ((hom.α_hom W (X.tensor Y) Z).comp ((hom.id W).tensor (hom.α_hom X Y Z))))
  ((hom.α_hom (W.tensor X) Y Z).comp (hom.α_hom W X (Y.tensor Z)))
| triangle {X Y} : hom_equiv ((hom.α_hom X unit Y).comp ((hom.id X).tensor (hom.l_hom Y)))
  ((hom.ρ_hom X).tensor (hom.id Y))

/-- We say that two formal morphisms in the free monoidal category are equivalent if they become
    equal if we apply the relations that are true in a monoidal category. Note that we will prove
    that there is only one equivalence class -- this is the monoidal coherence theorem. -/
def setoid_hom (X Y : F C) : setoid (X ⟶ᵐ Y) :=
⟨hom_equiv,
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

section functor
variables {D : Type u'} [category.{v'} D] [monoidal_category D] (f : C → D)

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def project_obj : F C → D
| (free_monoidal_category.of X) := f X
| free_monoidal_category.unit := 𝟙_ D
| (free_monoidal_category.tensor X Y) := project_obj X ⊗ project_obj Y

section
open hom

/-- Auxiliary definition for `free_monoidal_category.project`. -/
@[simp] def project_map_aux : Π {X Y : F C}, (X ⟶ᵐ Y) → (project_obj f X ⟶ project_obj f Y)
| _ _ (id _) := 𝟙 _
| _ _ (α_hom _ _ _) := (α_ _ _ _).hom
| _ _ (α_inv _ _ _) := (α_ _ _ _).inv
| _ _ (l_hom _) := (λ_ _).hom
| _ _ (l_inv _) := (λ_ _).inv
| _ _ (ρ_hom _) := (ρ_ _).hom
| _ _ (ρ_inv _) := (ρ_ _).inv
| _ _ (comp f g) := project_map_aux f ≫ project_map_aux g
| _ _ (hom.tensor f g) := project_map_aux f ⊗ project_map_aux g

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def project_map (X Y : F C) : (X ⟶ Y) → (project_obj f X ⟶ project_obj f Y) :=
quotient.lift (project_map_aux f)
begin
  intros f g h,
  induction h with X Y f X Y f g hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg
    W X Y Z f g f' g' _ _ hfg hfg',
  { refl },
  { exact hfg'.symm },
  { exact hfg.trans hgh },
  { simp only [project_map_aux, hf, hg] },
  { simp only [project_map_aux, hfg, hfg'] },
  { simp only [project_map_aux, category.comp_id] },
  { simp only [project_map_aux, category.id_comp] },
  { simp only [project_map_aux, category.assoc ] },
  { simp only [project_map_aux, monoidal_category.tensor_id], refl },
  { simp only [project_map_aux, monoidal_category.tensor_comp] },
  { simp only [project_map_aux, iso.hom_inv_id] },
  { simp only [project_map_aux, iso.inv_hom_id] },
  { simp only [project_map_aux, monoidal_category.associator_naturality] },
  { simp only [project_map_aux, iso.hom_inv_id] },
  { simp only [project_map_aux, iso.inv_hom_id] },
  { simp only [project_map_aux], dsimp [project_obj],
    exact monoidal_category.right_unitor_naturality _ },
  { simp only [project_map_aux, iso.hom_inv_id] },
  { simp only [project_map_aux, iso.inv_hom_id] },
  { simp only [project_map_aux], dsimp [project_obj],
    exact monoidal_category.left_unitor_naturality _ },
  { simp only [project_map_aux], exact monoidal_category.pentagon _ _ _ _ },
  { simp only [project_map_aux], exact monoidal_category.triangle _ _ }
end

end

/-- If `D` is a monoidal category and we have a function `C → D`, then we have a functor from the
    free monoidal category over `C` to the category `D`. -/
def project : monoidal_functor (F C) D :=
{ obj := project_obj f,
  map := project_map f,
  ε := 𝟙 _,
  μ := λ X Y, 𝟙 _ }

end functor

end

end free_monoidal_category

end category_theory
