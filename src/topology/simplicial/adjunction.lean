/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.adjunction
import topology.simplicial.singular
import topology.simplicial.realization

universe variables u

open category_theory

namespace sType
open Top simplex_category opposite

def adjunction_realization_singular : realization.{u} ⊣ singular.{u} :=
{ hom_equiv := λ S X, _,
  unit :=
  { app := λ S,
    { app := λ n s, show singular_standard_simplex.obj (n.unop) ⟶ _,
      begin
        refine _ ≫ category_theory.limits.colimit.ι _ ⟨skeletal_equivalence.inverse.obj n.unop, _⟩,
        { show S.obj ((skeletal_equivalence.inverse ⋙ skeletal_equivalence.functor).op.obj n),
          apply S.map _ s,
          refine (skeletal_equivalence.counit.app (unop n)).op },
        { dsimp [realization_obj_functor],
          apply singular_standard_simplex.map,
          exact (skeletal_equivalence.counit_inv.app (unop n)), }
      end,
      naturality' :=
      begin
        intros, dsimp, simp, ext1, dsimp, sorry,
      end },
    naturality' := _ },
  counit := _,
  hom_equiv_unit' := _,
  hom_equiv_counit' := _ }

end sType
