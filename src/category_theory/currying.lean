/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.products.bifunctor

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/
namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

variables {C : Type u₁} [category.{v₁} C]
          {D : Type u₂} [category.{v₂} D]
          {E : Type u₃} [category.{v₃} E]

/--
The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
def uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E) :=
{ obj := λ F,
  { obj := λ X, (F.obj X.1).obj X.2,
    map := λ X Y f, (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2,
    map_comp' := λ X Y Z f g,
    begin
      simp only [prod_comp_fst, prod_comp_snd, functor.map_comp,
                 nat_trans.comp_app, category.assoc],
      slice_lhs 2 3 { rw ← nat_trans.naturality },
      rw category.assoc,
    end },
  map := λ F G T,
  { app := λ X, (T.app X.1).app X.2,
    naturality' := λ X Y f,
    begin
      simp only [prod_comp_fst, prod_comp_snd, category.comp_id, category.assoc,
        functor.map_id, functor.map_comp, nat_trans.id_app, nat_trans.comp_app],
      slice_lhs 2 3 { rw nat_trans.naturality },
      slice_lhs 1 2 { rw [←nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app] },
      rw category.assoc,
    end } }.

/--
The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curry_obj (F : (C × D) ⥤ E) : C ⥤ (D ⥤ E) :=
{ obj := λ X,
    { obj := λ Y, F.obj (X, Y),
      map := λ Y Y' g, F.map (𝟙 X, g) },
    map := λ X X' f, { app := λ Y, F.map (f, 𝟙 Y) } }

/--
The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
def curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E)) :=
{ obj := λ F, curry_obj F,
  map := λ F G T,
  { app := λ X,
    { app := λ Y, T.app (X, Y),
      naturality' := λ Y Y' g,
      begin
        dsimp [curry_obj],
        rw nat_trans.naturality,
      end },
    naturality' := λ X X' f,
    begin
      ext, dsimp [curry_obj],
      rw nat_trans.naturality,
    end } }.

@[simp] lemma uncurry.obj_obj {F : C ⥤ (D ⥤ E)} {X : C × D} :
  (uncurry.obj F).obj X = (F.obj X.1).obj X.2 := rfl
@[simp] lemma uncurry.obj_map {F : C ⥤ (D ⥤ E)} {X Y : C × D} {f : X ⟶ Y} :
  (uncurry.obj F).map f = ((F.map f.1).app X.2) ≫ ((F.obj Y.1).map f.2) := rfl
@[simp] lemma uncurry.map_app {F G : C ⥤ (D ⥤ E)} {α : F ⟶ G} {X : C × D} :
  (uncurry.map α).app X = (α.app X.1).app X.2 := rfl
@[simp] lemma curry.obj_obj_obj
  {F : (C × D) ⥤ E} {X : C} {Y : D} :
  ((curry.obj F).obj X).obj Y = F.obj (X, Y) := rfl
@[simp] lemma curry.obj_obj_map
  {F : (C × D) ⥤ E} {X : C} {Y Y' : D} {g : Y ⟶ Y'} :
  ((curry.obj F).obj X).map g = F.map (𝟙 X, g) := rfl
@[simp] lemma curry.obj_map_app {F : (C × D) ⥤ E} {X X' : C} {f : X ⟶ X'} {Y} :
  ((curry.obj F).map f).app Y = F.map (f, 𝟙 Y) := rfl
@[simp] lemma curry.map_app_app {F G : (C × D) ⥤ E} {α : F ⟶ G} {X} {Y} :
  ((curry.map α).app X).app Y = α.app (X, Y) := rfl

/--
The equivalence of functor categories given by currying/uncurrying.
-/
@[simps] -- create projection simp lemmas even though this isn't a `{ .. }`.
def currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E) :=
equivalence.mk uncurry curry
  (nat_iso.of_components (λ F, nat_iso.of_components
    (λ X, nat_iso.of_components (λ Y, iso.refl _) (by tidy)) (by tidy)) (by tidy))
  (nat_iso.of_components (λ F, nat_iso.of_components
    (λ X, eq_to_iso (by simp)) (by tidy)) (by tidy))

end category_theory
