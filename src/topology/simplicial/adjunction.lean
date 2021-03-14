/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.adjunction
import topology.simplicial.singular
import topology.simplicial.realization

universe variables u

noncomputable theory
open category_theory

namespace sSet
open Top simplex_category opposite

@[simps]
def realization_singular_unit : 𝟭 sSet ⟶ realization.{u} ⋙ singular.{u} :=
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
  naturality' := sorry }

@[simps]
def singular_realization_counit : singular.{u} ⋙ realization.{u} ⟶ 𝟭 Top :=
{ app := λ X, category_theory.limits.colimit.desc (realization_obj_functor (singular.obj X))
    { X := X,
      ι :=
      { app := λ s,
        show singular_standard_simplex.obj _ ⟶ X, from
        ((standard_simplex_has_realization _).equiv X).symm
        { app := λ m i, singular_standard_simplex.map i ≫ s.2,
          naturality' := by { intros m n i, ext1, dsimp at *, } },
        naturality' := _ } } }

@[simps]
def adjunction_realization_singular : realization.{u} ⊣ singular.{u} :=
adjunction.mk_of_unit_counit
{ unit   := realization_singular_unit,
  counit := singular_realization_counit,
  left_triangle' :=
  begin
    ext S x,
    simp only [functor.associator_hom_app, id_app, singular_realization_counit_app,
      nat_trans.id_app', whisker_right_app, whisker_left_app, comp_app,
      category.id_comp, realization_map_2, nat_trans.comp_app],
    dsimp at *,
    dsimp [realization_obj, realization_obj_functor],
    simp,
    dsimp at x,
  end,
  right_triangle' := _ }
/-
{ hom_equiv := λ S X, _,
  unit := sorry,
  -- { app := λ S,
  --   { app := λ n s, show singular_standard_simplex.obj (n.unop) ⟶ _,
  --     begin
  --       refine _ ≫ category_theory.limits.colimit.ι _ ⟨skeletal_equivalence.inverse.obj n.unop, _⟩,
  --       { show S.obj ((skeletal_equivalence.inverse ⋙ skeletal_equivalence.functor).op.obj n),
  --         apply S.map _ s,
  --         refine (skeletal_equivalence.counit.app (unop n)).op },
  --       { dsimp [realization_obj_functor],
  --         apply singular_standard_simplex.map,
  --         exact (skeletal_equivalence.counit_inv.app (unop n)), }
  --     end,
  --     naturality' :=
  --     begin
  --       intros, dsimp, simp, ext1, dsimp, sorry,
  --     end },
  --   naturality' := sorry },
  counit :=
  { app := λ X, category_theory.limits.colimit.desc (realization_obj_functor (singular.obj X))
      { X := X,
        ι :=
        { app := λ s,
          show singular_standard_simplex.obj _ ⟶ X, from
          (equiv.of_bijective _ ((standard_simplex_has_realization _).w X)).inv_fun
          { app := λ m i, singular_standard_simplex.map i ≫ s.2,
            naturality' := by { intros m n i, ext1, dsimp at *, } },
          naturality' := _ } },
    naturality' := _ },
  hom_equiv_unit' := _,
  hom_equiv_counit' := _ }
-/

end sSet
