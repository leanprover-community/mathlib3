import category_theory.limits.preserves.shapes.kernels
import category_theory.abelian.basic

open category_theory
open category_theory.limits

universes u v

variables {C D : Type u} [category.{v} C] [category.{v} D] [abelian C] [abelian D] (F : C ⥤ D)
  [i : is_equivalence F] {X Y : C} (f : X ⟶ Y)

include i
example : preserves_limit (parallel_pair f 0) F :=
{ preserves := λ c hc,
  { lift := λ s, (functor.map_cone_map_cone_inv F s).inv.hom ≫ F.map (hc.lift (functor.map_cone_inv F s)),
    fac' := λ s j, begin
      rw [functor.map_cone_π_app, category.assoc, ← functor.map_comp, hc.fac',
        ← functor.map_cone_π_app, cone_morphism.w],
    end,
    uniq' := λ s m eq1, begin
      sorry
    end } }
