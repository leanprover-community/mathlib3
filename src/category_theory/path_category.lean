import category_theory.category

universes v₁ v₂ u₁ u₂

namespace category_theory

section

/--
A type synonym for the category of paths in a quiver.
-/
def paths (V : Type u₁) [quiver.{v₁} V] : Type u₁ := V

variables (V : Type u₁) [quiver.{v₁} V]

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

end paths

variables (W : Type u₂) [quiver.{v₂} W]

-- FIXME do we really need this?
@[simp] lemma prefunctor.map_path_comp' (F : prefunctor V W)
  {X Y Z : paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map_path (f ≫ g) = (F.map_path f).comp (F.map_path g) :=
prefunctor.map_path_comp _ _ _

end

section

variables {C : Type u} [category.{v} C]

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
