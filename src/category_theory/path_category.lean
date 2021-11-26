/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.eq_to_hom

/-!
# The category paths on a quiver.
-/

universes v₁ v₂ u₁ u₂

namespace category_theory

section

/--
A type synonym for the category of paths in a quiver.
-/
def paths (V : Type u₁) : Type u₁ := V

instance (V : Type u₁) [inhabited V] : inhabited (paths V) := ⟨(default V : V)⟩

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
lemma compose_path_comp {X Y Z : C} (f : path X Y) (g : path Y Z) :
  compose_path (f.comp g) = compose_path f ≫ compose_path g :=
begin
  induction g with Y' Z' g e ih,
  { simp, },
  { simp [ih], },
end

end

end category_theory
