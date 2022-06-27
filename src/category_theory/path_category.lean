/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.eq_to_hom
import category_theory.quotient
import combinatorics.quiver.path

/-!
# The category paths on a quiver.
When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

universes v₁ v₂ u₁ u₂

namespace category_theory

section

/--
A type synonym for the category of paths in a quiver.
-/
def paths (V : Type u₁) : Type u₁ := V

instance (V : Type u₁) [inhabited V] : inhabited (paths V) := ⟨(default : V)⟩

variables (V : Type u₁) [quiver.{v₁+1} V]

namespace paths

instance category_paths : category.{max u₁ v₁} (paths V) :=
{ hom := λ (X Y : V), quiver.path X Y,
  id := λ X, quiver.path.nil,
  comp := λ X Y Z f g, quiver.path.comp f g, }

variables {V}

/--
The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
def of : prefunctor V (paths V) :=
{ obj := λ X, X,
  map := λ X Y f, f.to_path, }

local attribute [ext] functor.ext

/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext]
lemma ext_functor {C} [category C]
  {F G : paths V ⥤ C}
  (h_obj : F.obj = G.obj)
  (h : ∀ (a b : V) (e : a ⟶ b), F.map e.to_path =
  eq_to_hom (congr_fun h_obj a) ≫ G.map e.to_path ≫ eq_to_hom (congr_fun h_obj.symm b)) :
  F = G :=
begin
  ext X Y f,
  { induction f with Y' Z' g e ih,
    { erw [F.map_id, G.map_id, category.id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { erw [F.map_comp g e.to_path, G.map_comp g e.to_path, ih, h],
      simp only [category.id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc, category.assoc], }, },
  { intro X, rw h_obj, }
end

end paths

variables (W : Type u₂) [quiver.{v₂+1} W]

-- A restatement of `prefunctor.map_path_comp` using `f ≫ g` instead of `f.comp g`.
@[simp] lemma prefunctor.map_path_comp' (F : prefunctor V W)
  {X Y Z : paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map_path (f ≫ g) = (F.map_path f).comp (F.map_path g) :=
prefunctor.map_path_comp _ _ _

end

section

variables {C : Type u₁} [category.{v₁} C]

open quiver

/-- A path in a category can be composed to a single morphism. -/
@[simp]
def compose_path {X : C} : Π {Y : C} (p : path X Y), X ⟶ Y
| _ path.nil := 𝟙 X
| _ (path.cons p e) := compose_path p ≫ e

@[simp]
lemma compose_path_to_path {X Y : C} (f : X ⟶ Y) : compose_path (f.to_path) = f :=
category.id_comp _

@[simp]
lemma compose_path_comp {X Y Z : C} (f : path X Y) (g : path Y Z) :
  compose_path (f.comp g) = compose_path f ≫ compose_path g :=
begin
  induction g with Y' Z' g e ih,
  { simp, },
  { simp [ih], },
end

@[simp]
lemma compose_path_id {X : paths C} : compose_path (𝟙 X) = 𝟙 X := rfl

@[simp]
lemma compose_path_comp' {X Y Z : paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  compose_path (f ≫ g) = compose_path f ≫ compose_path g :=
compose_path_comp f g

variables (C)

/-- Composition of paths as functor from the path category of a category to the category. -/
@[simps]
def path_composition : paths C ⥤ C :=
{ obj := λ X, X,
  map := λ X Y f, compose_path f, }

/-- The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism. -/
-- TODO: This, and what follows, should be generalized to
-- the `hom_rel` for the kernel of any functor.
-- Indeed, this should be part of an equivalence between congruence relations on a category `C`
-- and full, essentially surjective functors out of `C`.
@[simp]
def paths_hom_rel : hom_rel (paths C) :=
λ X Y p q, (path_composition C).map p = (path_composition C).map q

/-- The functor from a category to the canonical quotient of its path category. -/
@[simps]
def to_quotient_paths : C ⥤ quotient (paths_hom_rel C) :=
{ obj := λ X, quotient.mk X,
  map := λ X Y f, quot.mk _ f.to_path,
  map_id' := λ X, quot.sound (quotient.comp_closure.of _ _ _ (by simp)),
  map_comp' := λ X Y Z f g, quot.sound (quotient.comp_closure.of _ _ _ (by simp)), }

/-- The functor from the canonical quotient of a path category of a category
to the original category. -/
@[simps]
def quotient_paths_to : quotient (paths_hom_rel C) ⥤ C :=
quotient.lift _ (path_composition C) (λ X Y p q w, w)

/-- The canonical quotient of the path category of a category
is equivalent to the original category. -/
def quotient_paths_equiv : quotient (paths_hom_rel C) ≌ C :=
{ functor := quotient_paths_to C,
  inverse := to_quotient_paths C,
  unit_iso := nat_iso.of_components (λ X, by { cases X, refl, }) begin
    intros,
    cases X, cases Y,
    induction f,
    dsimp,
    simp only [category.comp_id, category.id_comp],
    apply quot.sound,
    apply quotient.comp_closure.of,
    simp [paths_hom_rel],
  end,
  counit_iso := nat_iso.of_components (λ X, iso.refl _) (by tidy),
  functor_unit_iso_comp' := by { intros, cases X, dsimp, simp, refl, }, }

end

end category_theory
