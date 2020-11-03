/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.presheaf
import category_theory.closed.cartesian

namespace category_theory

noncomputable theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type v₂} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

open colimit_adj

section cartesian_closed

def prod_preserves_colimits [has_finite_products D] [has_colimits D]
  [∀ (X : D), preserves_colimits (prod.functor.obj X)]
  (F : C ⥤ D) :
  preserves_colimits (prod.functor.obj F) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ K,
    { preserves := λ c t,
      begin
        apply evaluation_jointly_reflects_colimits,
        intro k,
        change is_colimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).map_cocone c),
        let := is_colimit_of_preserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t,
        apply is_colimit.map_cocone_equiv _ this,
        apply (nat_iso.of_components _ _).symm,
        { intro G,
          apply as_iso (prod_comparison ((evaluation C D).obj k) F G) },
        { intros G G',
          apply prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) },
      end } } }

end cartesian_closed

end category_theory
