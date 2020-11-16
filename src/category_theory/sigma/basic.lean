/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.natural_isomorphism
import category_theory.eq_to_hom
import data.sigma.basic
import category_theory.pi.basic

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace category_theory
namespace sigma

universes w₀ w₁ w₂ v₁ v₂ u₁ u₂

variables {I : Type w₀} {C : I → Type u₁} [Π i, category.{v₁} (C i)]

inductive sigma_hom : (Σ i, C i) → (Σ i, C i) → Type (max w₀ v₁ u₁)
| matched : Π (i : I) (X Y : C i), (X ⟶ Y) → sigma_hom ⟨_, X⟩ ⟨_, Y⟩

namespace sigma_hom

def id : Π (X : Σ i, C i), sigma_hom X X
| ⟨i, X⟩ := matched i _ _ (𝟙 _)

def comp : Π {X Y Z : Σ i, C i}, sigma_hom X Y → sigma_hom Y Z → sigma_hom X Z
| _ _ _ (matched _ X _ f) (matched i Y Z g) := matched _ _ _ (f ≫ g)

instance : category_struct (Σ i, C i) :=
{ hom := sigma_hom,
  id := id,
  comp := λ X Y Z f g, comp f g }

@[simp]
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) :
  comp (matched i X Y f) (matched i Y Z g) = matched i X Z (f ≫ g) :=
rfl

lemma assoc : ∀ (X Y Z W : Σ i, C i) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
| _ _ _ _ (matched _ X _ f) (matched _ Y _ g) (matched i Z W h) :=
  begin
    change matched _ _ _ _ = matched _ _ _ _,
    simp,
  end

lemma id_comp : ∀ (X Y : Σ i, C i) (f : X ⟶ Y), 𝟙 X ≫ f = f
| _ _ (matched i X Y f) :=
  begin
    change matched _ _ _ _ = matched _ _ _ _,
    simp,
  end

lemma comp_id : ∀ (X Y : Σ i, C i) (f : X ⟶ Y), f ≫ 𝟙 Y = f
| _ _ (matched i X Y f) :=
  begin
    change matched _ _ _ _ = matched _ _ _ _,
    simp,
  end

end sigma_hom

instance sigma : category (Σ i, C i) :=
{ id_comp' := sigma_hom.id_comp,
  comp_id' := sigma_hom.comp_id,
  assoc' := sigma_hom.assoc }

/-- The inclusion functor into the disjoint union of categories. -/
@[simps]
def incl (i : I) : C i ⥤ Σ i, C i :=
{ obj := λ X, ⟨i, X⟩,
  map := λ X Y f, sigma_hom.matched _ _ _ f }

instance (i : I) : full (incl i : C i ⥤ Σ i, C i) :=
{ preimage := λ X Y ⟨_, _, _, f⟩, f,
  witness' := λ X Y ⟨_, _, _, f⟩, rfl }.

instance (i : I) : faithful (incl i : C i ⥤ Σ i, C i) := {}.

section
variables {D : Type u₂} [category.{v₂} D] (F : Π i, C i ⥤ D)

def desc_map : ∀ (X Y : Σ i, C i), (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
| _ _ (sigma_hom.matched i X Y g) := (F i).map g

@[simps]
def desc : (Σ i, C i) ⥤ D :=
{ obj := λ X, (F X.1).obj X.2,
  map := λ X Y g, desc_map F X Y g,
  map_id' := λ X,
  begin
    cases X with i X,
    apply (F i).map_id,
  end,
  map_comp' :=
  begin
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨i, _, Y, f⟩ ⟨_, _, Z, g⟩,
    apply (F i).map_comp,
  end }

def incl_desc (i : I) : incl i ⋙ desc F ≅ F i :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

def desc_uniq (q : (Σ i, C i) ⥤ D) (h : Π i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
nat_iso.of_components (λ ⟨i, X⟩, (h i).app X)
begin
  rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩,
  apply (h i).hom.naturality f,
end

def desc_hom_ext (q₁ q₂ : (Σ i, C i) ⥤ D) (h : Π i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) :
  q₁ ≅ q₂ :=
desc_uniq (λ i, incl i ⋙ q₂) q₁ h ≪≫ (desc_uniq _ _ (λ i, iso.refl _)).symm

@[simps]
def joining (F G : (Σ i, C i) ⥤ D) (h : Π (i : I), incl i ⋙ F ⟶ incl i ⋙ G): F ⟶ G :=
{ app :=
  begin
    rintro ⟨j, X⟩,
    apply (h j).app X,
  end,
  naturality' :=
  begin
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩,
    apply (h j).naturality,
  end }


end

section

variables (C) {J : Type w₁}

@[simps {rhs_md := semireducible}]
def map (h : J → I) : (Σ (j : J), C (h j)) ⥤ (Σ (i : I), C i) :=
desc (λ j, incl (h j))

def incl_comp_map (h : J → I) (j : J) : incl j ⋙ map C h ≅ incl (h j) :=
incl_desc _ _

variable (I)

def map_id : map C (id : I → I) ≅ 𝟭 (Σ i, C i) :=
desc_hom_ext _ _ (λ i, nat_iso.of_components (λ X, iso.refl _) (by tidy))

variables {I} {K : Type w₂}

def map_comp (f : K → J) (g : J → I) : map (C ∘ g) f ⋙ (map C g : _) ≅ map C (g ∘ f) :=
desc_uniq _ _ $ λ k,
  (iso_whisker_right (incl_comp_map (C ∘ g) f k) (map C g : _) : _) ≪≫ incl_comp_map _ _ _

end

namespace functor

variables {C}
variables {D : I → Type u₁} [∀ i, category.{v₁} (D i)]

/--
Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma (F : Π i, C i ⥤ D i) : (Σ i, C i) ⥤ (Σ i, D i) :=
desc (λ i, F i ⋙ incl i)

end functor

namespace nat_trans

variables {C}
variables {D : I → Type u₁} [∀ i, category.{v₁} (D i)]
variables {F G : Π i, C i ⥤ D i}

/--
Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def sigma (α : Π i, F i ⟶ G i) : functor.sigma F ⟶ functor.sigma G :=
{ app := λ f, sigma_hom.matched _ _ _ ((α f.1).app _),
  naturality' :=
  begin
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩,
    change sigma_hom.matched _ _ _ _ = sigma_hom.matched _ _ _ _,
    rw (α i).naturality,
  end }

end nat_trans

end sigma
end category_theory
