import category_theory.presheaf
import category_theory.instances.TopCommRing

universes v u

open category_theory
open category_theory.instances
open topological_space

open category_theory
open category_theory.instances
open topological_space

namespace category_theory.presheaf_on_space

variables (X : Top.{v})

def presheaf_of_functions_to (T : Top.{v}) : presheaf_on_space (Type v) X :=
(opens.as_Top X).op ⋙ (yoneda.obj T)

instance {α : Type u} {β : Type v} [topological_space α] [topological_space β] [has_mul β] : has_mul (subtype (@continuous α β _ _)) :=
{ mul := λ f g, ⟨f.1 * g.1, by { have fp := f.2, have gp := g.2, library_search }⟩  }

def functions (X : Top) (R : TopCommRing) : CommRing :=
{ α := X ⟶ (TopCommRing.forget_to_Top.obj R),
  str := begin dsimp [(⟶)], apply_instance, end,}

def not_yoneda : TopCommRing ⥤ (Topᵒᵖ ⥤ CommRing) :=
{ obj := λ R,
  { obj := λ X, sorry,
    map := λ X Y f, sorry },
  map := sorry, }

def presheaf_of_functions_to_TopCommRing (T : TopCommRing.{v}) :
  presheaf_on_space TopCommRing.{v} X :=
sorry

end category_theory.presheaf_on_space
