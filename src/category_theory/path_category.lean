import category_theory.category

universes v u

open category_theory

/--
A type synonym for the category of paths in a quiver.
-/
def paths (V : Type u) [quiver.{v} V] : Type u := V

instance category_paths (V : Type u) [quiver.{v} V] : category.{max u v} (paths V) :=
{ hom := λ (X Y : V), quiver.path X Y,
  id := λ X, quiver.path.nil,
  comp := λ X Y Z f g, quiver.path.comp f g, }
