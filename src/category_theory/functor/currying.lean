/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.products.bifunctor

/-!
# Curry and uncurry, as functors.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/
namespace category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {B : Type u₁} [category.{v₁} B]
          {C : Type u₂} [category.{v₂} C]
          {D : Type u₃} [category.{v₃} D]
          {E : Type u₄} [category.{v₄} E]

/--
The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps]
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
@[simps obj_obj_obj obj_obj_map obj_map_app map_app_app]
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

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps]
def flip_iso_curry_swap_uncurry (F : C ⥤ D ⥤ E) :
  F.flip ≅ curry.obj (prod.swap _ _ ⋙ uncurry.obj F) :=
nat_iso.of_components (λ d, nat_iso.of_components (λ c, iso.refl _) (by tidy)) (by tidy)

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps]
def uncurry_obj_flip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ prod.swap _ _ ⋙ uncurry.obj F :=
nat_iso.of_components (λ p, iso.refl _) (by tidy)

variables (B C D E)

/--
A version of `category_theory.whiskering_right` for bifunctors, obtained by uncurrying,
applying `whiskering_right` and currying back
-/
@[simps] def whiskering_right₂ : (C ⥤ D ⥤ E) ⥤ ((B ⥤ C) ⥤ (B ⥤ D) ⥤ (B ⥤ E)) :=
uncurry ⋙ (whiskering_right _ _ _) ⋙
((whiskering_left _ _ _).obj (prod_functor_to_functor_prod _ _ _)) ⋙ curry

end category_theory
