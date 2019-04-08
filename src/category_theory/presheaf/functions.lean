import category_theory.presheaf
import category_theory.instances.TopCommRing

universes v u

open category_theory
open category_theory.instances

namespace category_theory.presheaf_on_space

variables (X : Top.{v})

def presheaf_of_functions_to (T : Top.{v}) : presheaf_on_space (Type v) X :=
{ obj := λ U, sorry,
  map := λ U V i, sorry }

def presheaf_of_functions_to_CommRing (T : TopCommRing.{v}) := sorry

end category_theory.presheaf_on_space
