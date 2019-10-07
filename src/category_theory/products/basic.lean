/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.equivalence
import category_theory.eq_to_hom
import tactic.interactive

namespace category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ -- declare the `v`'s first; see `category_theory.category` for an explanation

section
variables (C : Type u₁) [𝒞 : category.{v₁} C] (D : Type u₂) [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/--
`prod C D` gives the cartesian product of two categories.
-/
instance prod : category.{max v₁ v₂} (C × D) :=
{ hom     := λ X Y, ((X.1) ⟶ (Y.1)) × ((X.2) ⟶ (Y.2)),
  id      := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
  comp    := λ _ _ _ f g, (f.1 ≫ g.1, f.2 ≫ g.2) }

-- rfl lemmas for category.prod
@[simp] lemma prod_id (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := rfl
@[simp] lemma prod_comp {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) :
  f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl
@[simp] lemma prod_id_fst (X : prod C D) : _root_.prod.fst (𝟙 X) = 𝟙 X.fst := rfl
@[simp] lemma prod_id_snd (X : prod C D) : _root_.prod.snd (𝟙 X) = 𝟙 X.snd := rfl
@[simp] lemma prod_comp_fst {X Y Z : prod C D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).1 = f.1 ≫ g.1 := rfl
@[simp] lemma prod_comp_snd {X Y Z : prod C D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).2 = f.2 ≫ g.2 := rfl
end

section
variables (C : Type u₁) [𝒞 : category.{v₁} C] (D : Type u₁) [𝒟 : category.{v₁} D]
include 𝒞 𝒟
/--
`prod.category.uniform C D` is an additional instance specialised so both factors have the same universe levels. This helps typeclass resolution.
-/
instance uniform_prod : category (C × D) := category_theory.prod C D
end

-- Next we define the natural functors into and out of product categories. For now this doesn't address the universal properties.
namespace prod

variables (C : Type u₁) [𝒞 : category.{v₁} C] (D : Type u₂) [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/-- `inl C Z` is the functor `X ↦ (X, Z)`. -/
def inl (Z : D) : C ⥤ C × D :=
{ obj := λ X, (X, Z),
  map := λ X Y f, (f, 𝟙 Z) }

@[simp] lemma inl_obj (Z : D) (X : C) : (inl C D Z).obj X = (X, Z) := rfl
@[simp] lemma inl_map (Z : D) {X Y : C} {f : X ⟶ Y} : (inl C D Z).map f = (f, 𝟙 Z) := rfl

/-- `inr D Z` is the functor `X ↦ (Z, X)`. -/
def inr (Z : C) : D ⥤ C × D :=
{ obj := λ X, (Z, X),
  map := λ X Y f, (𝟙 Z, f) }

@[simp] lemma inr_obj (Z : C) (X : D) : (inr C D Z).obj X = (Z, X) := rfl
@[simp] lemma inr_map (Z : C) {X Y : D} {f : X ⟶ Y} : (inr C D Z).map f = (𝟙 Z, f) := rfl

/-- `fst` is the functor `(X, Y) ↦ X`. -/
def fst : C × D ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1 }

@[simp] lemma fst_obj (X : C × D) : (fst C D).obj X = X.1 := rfl
@[simp] lemma fst_map {X Y : C × D} {f : X ⟶ Y} : (fst C D).map f = f.1 := rfl

/-- `snd` is the functor `(X, Y) ↦ Y`. -/
def snd : C × D ⥤ D :=
{ obj := λ X, X.2,
  map := λ X Y f, f.2 }

@[simp] lemma snd_obj (X : C × D) : (snd C D).obj X = X.2 := rfl
@[simp] lemma snd_map {X Y : C × D} {f : X ⟶ Y} : (snd C D).map f = f.2 := rfl

def swap : C × D ⥤ D × C :=
{ obj := λ X, (X.2, X.1),
  map := λ _ _ f, (f.2, f.1) }

@[simp] lemma swap_obj (X : C × D) : (swap C D).obj X = (X.2, X.1) := rfl
@[simp] lemma swap_map {X Y : C × D} {f : X ⟶ Y} : (swap C D).map f = (f.2, f.1) := rfl

def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C × D) :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }

def braiding : C × D ≌ D × C :=
equivalence.mk (swap C D) (swap D C)
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))

instance swap_is_equivalence : is_equivalence (swap C D) :=
(by apply_instance : is_equivalence (braiding C D).functor)

end prod

section
variables (C : Type u₁) [𝒞 : category.{v₁} C] (D : Type u₂) [𝒟 : category.{v₂} D]
include 𝒞 𝒟

def evaluation : C ⥤ (C ⥤ D) ⥤ D :=
{ obj := λ X,
  { obj := λ F, F.obj X,
    map := λ F G α, α.app X, },
  map := λ X Y f,
  { app := λ F, F.map f,
    naturality' := λ F G α, eq.symm (α.naturality f) } }

@[simp] lemma evaluation_obj_obj (X) (F) : ((evaluation C D).obj X).obj F = F.obj X := rfl
@[simp] lemma evaluation_obj_map (X) {F G} (α : F ⟶ G) :
  ((evaluation C D).obj X).map α = α.app X := rfl
@[simp] lemma evaluation_map_app {X Y} (f : X ⟶ Y) (F) :
  ((evaluation C D).map f).app F = F.map f := rfl

def evaluation_uncurried : C × (C ⥤ D) ⥤ D :=
{ obj := λ p, p.2.obj p.1,
  map := λ x y f, (x.2.map f.1) ≫ (f.2.app y.1),
  map_comp' := λ X Y Z f g,
  begin
    cases g, cases f, cases Z, cases Y, cases X,
    simp only [prod_comp, nat_trans.comp_app, functor.map_comp, category.assoc],
    rw [←nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app,
        category.assoc, nat_trans.naturality],
  end }

@[simp] lemma evaluation_uncurried_obj (p) : (evaluation_uncurried C D).obj p = p.2.obj p.1 := rfl
@[simp] lemma evaluation_uncurried_map {x y} (f : x ⟶ y) :
  (evaluation_uncurried C D).map f = (x.2.map f.1) ≫ (f.2.app y.1) := rfl

end

variables {A : Type u₁} [𝒜 : category.{v₁} A]
          {B : Type u₂} [ℬ : category.{v₂} B]
          {C : Type u₃} [𝒞 : category.{v₃} C]
          {D : Type u₄} [𝒟 : category.{v₄} D]
include 𝒜 ℬ 𝒞 𝒟

namespace functor
/-- The cartesian product of two functors. -/
def prod (F : A ⥤ B) (G : C ⥤ D) : A × C ⥤ B × D :=
{ obj := λ X, (F.obj X.1, G.obj X.2),
  map := λ _ _ f, (F.map f.1, G.map f.2) }

/- Because of limitations in Lean 3's handling of notations, we do not setup a notation `F × G`.
   You can use `F.prod G` as a "poor man's infix", or just write `functor.prod F G`. -/

@[simp] lemma prod_obj (F : A ⥤ B) (G : C ⥤ D) (a : A) (c : C) :
  (F.prod G).obj (a, c) = (F.obj a, G.obj c) := rfl
@[simp] lemma prod_map (F : A ⥤ B) (G : C ⥤ D) {a a' : A} {c c' : C} (f : (a, c) ⟶ (a', c')) :
  (F.prod G).map f = (F.map f.1, G.map f.2) := rfl
end functor

namespace nat_trans

/-- The cartesian product of two natural transformations. -/
def prod {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.prod H ⟶ G.prod I :=
{ app         := λ X, (α.app X.1, β.app X.2),
  naturality' := λ X Y f,
  begin
    cases X, cases Y,
    simp only [functor.prod_map, prod.mk.inj_iff, prod_comp],
    split; rw naturality
  end }

/- Again, it is inadvisable in Lean 3 to setup a notation `α × β`;
   use instead `α.prod β` or `nat_trans.prod α β`. -/

@[simp] lemma prod_app  {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) (c : C) :
  (nat_trans.prod α β).app (a, c) = (α.app a, β.app c) := rfl
end nat_trans

end category_theory
