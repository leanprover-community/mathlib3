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
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/

namespace category_theory
namespace sigma

universes w₁ w₂ w₃ v₁ v₂ u₁ u₂

variables {I : Type w₁} {C : I → Type u₁} [Π i, category.{v₁} (C i)]

/--
The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : C j`, a morphism
`(i, X) ⟶ (j, Y)` if `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` there are no such morphisms.
-/
inductive sigma_hom : (Σ i, C i) → (Σ i, C i) → Type (max w₁ v₁ u₁)
| mk : Π {i : I} {X Y : C i}, (X ⟶ Y) → sigma_hom ⟨i, X⟩ ⟨i, Y⟩

namespace sigma_hom

/-- The identity morphism on an object. -/
def id : Π (X : Σ i, C i), sigma_hom X X
| ⟨i, X⟩ := mk (𝟙 _)

instance (X : Σ i, C i) : inhabited (sigma_hom X X) := ⟨id X⟩

/-- Composition of sigma homomorphisms. -/
def comp : Π {X Y Z : Σ i, C i}, sigma_hom X Y → sigma_hom Y Z → sigma_hom X Z
| _ _ _ (mk f) (mk g) := mk (f ≫ g)

instance : category_struct (Σ i, C i) :=
{ hom := sigma_hom,
  id := id,
  comp := λ X Y Z f g, comp f g }

@[simp]
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) :
  comp (mk f) (mk g) = mk (f ≫ g) :=
rfl

lemma assoc : ∀ (X Y Z W : Σ i, C i) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
| _ _ _ _ (mk f) (mk g) (mk h) :=
  begin
    change mk ((f ≫ g) ≫ h) = mk (f ≫ g ≫ h),
    rw [category.assoc],
  end

lemma id_comp : ∀ (X Y : Σ i, C i) (f : X ⟶ Y), 𝟙 X ≫ f = f
| _ _ (mk f) :=
  begin
    change mk (𝟙 _ ≫ f) = mk f,
    rw [category.id_comp],
  end

lemma comp_id : ∀ (X Y : Σ i, C i) (f : X ⟶ Y), f ≫ 𝟙 Y = f
| _ _ (mk f) :=
  begin
    change mk (f ≫ 𝟙 _) = mk f,
    rw [category.comp_id],
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
  map := λ X Y, sigma_hom.mk }

instance (i : I) : full (incl i : C i ⥤ Σ i, C i) :=
{ preimage := λ X Y ⟨f⟩, f,
  witness' := λ X Y ⟨f⟩, rfl }.

instance (i : I) : faithful (incl i : C i ⥤ Σ i, C i) := {}.

section
variables {D : Type u₂} [category.{v₂} D] (F : Π i, C i ⥤ D)

/-- (Implementation). An auxiliary definition -/
def desc_map : ∀ (X Y : Σ i, C i), (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
| _ _ (sigma_hom.mk g) := (F _).map g

/--
Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
def desc : (Σ i, C i) ⥤ D :=
{ obj := λ X, (F X.1).obj X.2,
  map := λ X Y g, desc_map F X Y g,
  map_id' := by { rintro ⟨i, X⟩, apply (F i).map_id },
  map_comp' := by { rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨i, _, Y, f⟩ ⟨_, _, Z, g⟩, apply (F i).map_comp } }

@[simp]
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) :
  (desc F).map (sigma_hom.mk f) = (F i).map f :=
rfl

/--
This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
-- We hand-generate the simp lemmas about this since they come out cleaner.
def incl_desc (i : I) : incl i ⋙ desc F ≅ F i :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

@[simp]
lemma incl_desc_hom_app (i : I) (X : C i) :
  (incl_desc F i).hom.app X = 𝟙 ((F i).obj X) :=
rfl

@[simp]
lemma incl_desc_inv_app (i : I) (X : C i) :
  (incl_desc F i).inv.app X = 𝟙 ((F i).obj X) :=
rfl

def desc_uniq (q : (Σ i, C i) ⥤ D) (h : Π i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
nat_iso.of_components (λ ⟨i, X⟩, (h i).app X) $
  by { rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩, apply (h i).hom.naturality f }

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

variables (C) {J : Type w₂}

@[simps {rhs_md := semireducible}]
def map (h : J → I) : (Σ (j : J), C (h j)) ⥤ (Σ (i : I), C i) :=
desc (λ j, incl (h j))

def incl_comp_map (h : J → I) (j : J) : incl j ⋙ map C h ≅ incl (h j) :=
incl_desc _ _

variable (I)

def map_id : map C (id : I → I) ≅ 𝟭 (Σ i, C i) :=
desc_hom_ext _ _ (λ i, nat_iso.of_components (λ X, iso.refl _) (by tidy))

variables {I} {K : Type w₃}

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
{ app := λ f, sigma_hom.mk ((α f.1).app _),
  naturality' :=
  begin
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩,
    change sigma_hom.mk _ = sigma_hom.mk _,
    rw (α i).naturality,
  end }

end nat_trans

end sigma
end category_theory
