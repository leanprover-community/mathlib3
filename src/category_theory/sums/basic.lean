/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.eq_to_hom

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/

namespace category_theory

universes v₁ u₁ -- morphism levels before object levels. See note [category_theory universes].

open sum

section
variables (C : Type u₁) [category.{v₁} C] (D : Type u₁) [category.{v₁} D]

/--
`sum C D` gives the direct sum of two categories.
-/
instance sum : category.{v₁} (C ⊕ D) :=
{ hom :=
    λ X Y, match X, Y with
    | inl X, inl Y := X ⟶ Y
    | inl X, inr Y := pempty
    | inr X, inl Y := pempty
    | inr X, inr Y := X ⟶ Y
    end,
  id :=
    λ X, match X with
    | inl X := 𝟙 X
    | inr X := 𝟙 X
    end,
  comp :=
    λ X Y Z f g, match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g := f ≫ g
    | inr X, inr Y, inr Z, f, g := f ≫ g
    end }

@[simp] lemma sum_comp_inl {P Q R : C} (f : (inl P : C ⊕ D) ⟶ inl Q)
  (g : (inl Q : C ⊕ D) ⟶ inl R) :
  @category_struct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
  @category_struct.comp _ _ (inl P) (inl Q) (inl R) (f : P ⟶ Q) (g : Q ⟶ R) := rfl
@[simp] lemma sum_comp_inr {P Q R : D} (f : (inr P : C ⊕ D) ⟶ inr Q)
  (g : (inr Q : C ⊕ D) ⟶ inr R) :
  @category_struct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
  @category_struct.comp _ _ (inr P) (inr Q) (inr R) (f : P ⟶ Q) (g : Q ⟶ R) := rfl
end

namespace sum

variables (C : Type u₁) [category.{v₁} C] (D : Type u₁) [category.{v₁} D]

/-- `inl_` is the functor `X ↦ inl X`. -/
-- Unfortunate naming here, suggestions welcome.
@[simps] def inl_ : C ⥤ C ⊕ D :=
{ obj := λ X, inl X,
  map := λ X Y f, f }

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps] def inr_ : D ⥤ C ⊕ D :=
{ obj := λ X, inr X,
  map := λ X Y f, f }

/-- The functor exchanging two direct summand categories. -/
def swap : C ⊕ D ⥤ D ⊕ C :=
{ obj :=
    λ X, match X with
    | inl X := inr X
    | inr X := inl X
    end,
  map :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := f
    | inr X, inr Y, f := f
    end }

@[simp] lemma swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X := rfl
@[simp] lemma swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X := rfl
@[simp] lemma swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f := rfl
@[simp] lemma swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f := rfl

namespace swap

/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
def equivalence : C ⊕ D ≌ D ⊕ C :=
equivalence.mk (swap C D) (swap D C)
  (nat_iso.of_components (λ X, eq_to_iso (by { cases X; refl })) (by tidy))
  (nat_iso.of_components (λ X, eq_to_iso (by { cases X; refl })) (by tidy))

instance is_equivalence : is_equivalence (swap C D) :=
(by apply_instance : is_equivalence (equivalence C D).functor)

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C ⊕ D) :=
(equivalence C D).unit_iso.symm

end swap

end sum

variables {A : Type u₁} [category.{v₁} A]
          {B : Type u₁} [category.{v₁} B]
          {C : Type u₁} [category.{v₁} C]
          {D : Type u₁} [category.{v₁} D]

namespace functor

/-- The sum of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D :=
{ obj :=
    λ X, match X with
    | inl X := inl (F.obj X)
    | inr X := inr (G.obj X)
    end,
  map :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := F.map f
    | inr X, inr Y, f := G.map f
    end,
  map_id' := λ X, begin cases X; unfold_aux, erw F.map_id, refl, erw G.map_id, refl end,
  map_comp' :=
    λ X Y Z f g, match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g := by { unfold_aux, erw F.map_comp, refl }
    | inr X, inr Y, inr Z, f, g := by { unfold_aux, erw G.map_comp, refl }
    end }

@[simp] lemma sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) :
  (F.sum G).obj (inl a) = inl (F.obj a) := rfl
@[simp] lemma sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) :
  (F.sum G).obj (inr c) = inr (G.obj c) := rfl
@[simp] lemma sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
  (F.sum G).map f = F.map f := rfl
@[simp] lemma sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
  (F.sum G).map f = G.map f := rfl
end functor

namespace nat_trans

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I :=
{ app         :=
    λ X, match X with
    | inl X := α.app X
    | inr X := β.app X
    end,
  naturality' :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := begin unfold_aux, erw α.naturality, refl, end
    | inr X, inr Y, f := begin unfold_aux, erw β.naturality, refl, end
    end }

@[simp] lemma sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
  (sum α β).app (inl a) = α.app a := rfl
@[simp] lemma sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
  (sum α β).app (inr c) = β.app c := rfl
end nat_trans

end category_theory
