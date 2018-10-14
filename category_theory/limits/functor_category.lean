-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u v

variables {J : Type v} [small_category J] {C : Type v} [small_category C] {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def switched (F : J ⥤ (C ⥤ D)) : C ⥤ (J ⥤ D) :=
{ obj := λ c,
  { obj := λ j, (F j) c,
    map' := λ j j' f, (F.map f) c,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [functor.map_comp, ←functor.category.comp_app] },
  map' := λ c c' f, { app := λ j, (F j).map f, naturality' := λ X Y g, by dsimp; rw ←nat_trans.naturality } }.

@[simp] lemma switched_obj_map (F : J ⥤ (C ⥤ D)) {j j' : J} (f : j ⟶ j') (X : C) : ((switched F) X).map f = (F.map f) X := rfl

def limit_cone_in_functor_category [has_limits.{u v} D] (F : J ⥤ (C ⥤ D)) : cone F :=
{ X := ((switched F) ⋙ lim),
  π := λ j, { app := λ X : C, (limit.cone (switched F X)).π j },
  w' := λ j j' f, begin ext1, dsimp at *, rw ←switched_obj_map, erw limits.cone.w, refl end }.

instance [has_limits.{u v} D] : has_limits.{(max u v) v} (C ⥤ D) :=
{ cone := λ J 𝒥 F, begin resetI, exact limit_cone_in_functor_category F end,
  is_limit := λ J 𝒥 F, begin resetI, exact
  { lift := λ s, { app := λ X, (limit.cone_morphism (switched F X)
                     { X := s.X X,
                       π := λ j, (s.π j) X,
                       w' := λ j j' f, by erw [←functor.category.comp_app, limits.cone.w] }).hom,
                   naturality' := λ X Y f,
                    begin
                     ext1, simp, dsimp [limit_cone_in_functor_category],
                     rw [limit.lift_π, ←category.assoc, limit.lift_π, (s.π j).naturality]
                    end, },
    fac' := λ s j, begin ext1, dsimp, erw limits.is_limit.fac end,
    uniq' := λ s m w, begin ext1, ext1, simp, rw ←w, refl, end } end
}

end category_theory.limits