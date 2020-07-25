--move this

import category_theory.functor_category
import category_theory.whiskering

namespace category_theory

variables {C D E : Type*} [category C] [category D] [category E]

def functor.comp_left (F : C ⥤ D) :
  (D ⥤ E) ⥤ (C ⥤ E) :=
{ obj := λ G, F ⋙ G,
  map := λ G₁ G₂ f, whisker_left F f }

end category_theory
