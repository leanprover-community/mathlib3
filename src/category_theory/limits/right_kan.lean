/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.types
import category_theory.punit
import category_theory.limits.functor_category

namespace category_theory
noncomputable theory

open category limits

universes v u₁ u₂ u₃
variables {C : Type v} {C' : Type u₂} {D : Type u₃}
variables [category.{v} C] [category.{v} C'] [category.{v} D]

def left_kan_obj (F : C ⥤ D) (p : C ⥤ C') [has_colimits D] :
  C' ⥤ D :=
{ obj := λ c', colimit (comma.fst p (functor.from_punit c') ⋙ F),
  map := λ X Y f,
  begin
    let Q : comma p (functor.from_punit X) ⥤ comma p (functor.from_punit Y),
      refine comma.map_right _ { app := λ _, f },
    refine colimit.desc _ ⟨_, λ K, _, _⟩,
    { refine _ ≫ colimit.ι _ (Q.obj K),
      exact 𝟙 _ },
    { intros h k α,
      simp,


    }


  end,
  map_id' := sorry,
  map_comp' := sorry

}

end category_theory
