-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.instances.CommRing.basic
import category_theory.limits.types
import category_theory.limits.preserves
import ring_theory.subring
import algebra.pi_instances

open category_theory
open category_theory.limits

universe u

#check instances.CommRing

namespace CommRing

variables {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRing.{u}) (j) : comm_ring ((F ⋙ CommRing.forget).obj j) :=
by { dsimp, apply_instance }
instance is_ring_hom_map (F : J ⥤ CommRing.{u}) (j j') (f : j ⟶ j') : is_ring_hom ((F ⋙ CommRing.forget).map f) :=
by { dsimp, apply_instance }

instance sections_submonoid (F : J ⥤ CommRing.{u}) : is_submonoid (F ⋙ forget).sections :=
{ one_mem := λ j j' f,
  begin
    simp only [functor.comp_map],
    erw is_ring_hom.map_one (CommRing.forget.map (F.map f)),
    refl,
  end,
  mul_mem := λ a b ah bh j j' f,
  begin
    simp only [functor.comp_map],
    erw is_ring_hom.map_mul (CommRing.forget.map (F.map f)),
    dsimp [functor.sections] at ah,
    rw ah f,
    dsimp [functor.sections] at bh,
    rw bh f,
    refl,
  end }

instance sections_add_submonoid (F : J ⥤ CommRing.{u}) : is_add_submonoid (F ⋙ forget).sections :=
{ zero_mem := λ j j' f,
  begin
    simp only [functor.comp_map],
    erw is_ring_hom.map_zero (CommRing.forget.map (F.map f)),
    refl,
  end,
  add_mem := λ a b ah bh j j' f,
  begin
    simp only [functor.comp_map],
    erw is_ring_hom.map_add (CommRing.forget.map (F.map f)),
    dsimp [functor.sections] at ah,
    rw ah f,
    dsimp [functor.sections] at bh,
    rw bh f,
    refl,
  end }

instance sections_add_subgroup (F : J ⥤ CommRing.{u}) : is_add_subgroup (F ⋙ forget).sections :=
{ neg_mem := λ a ah j j' f,
  begin
    simp only [functor.comp_map],
    erw is_ring_hom.map_neg (CommRing.forget.map (F.map f)),
    dsimp [functor.sections] at ah,
    rw ah f,
    refl,
  end,
  ..(CommRing.sections_add_submonoid F) }

instance sections_subring (F : J ⥤ CommRing.{u}) : is_subring (F ⋙ forget).sections :=
{ ..(CommRing.sections_submonoid F),
  ..(CommRing.sections_add_subgroup F) }

instance limit_comm_ring (F : J ⥤ CommRing.{u}) : comm_ring (limit (F ⋙ forget)) :=
@subtype.comm_ring ((Π (j : J), (F ⋙ forget).obj j)) (by apply_instance) _
  (by convert (CommRing.sections_subring F))

instance limit_π_is_ring_hom (F : J ⥤ CommRing.{u}) (j) : is_ring_hom (limit.π (F ⋙ CommRing.forget) j) :=
{ map_one := by { simp only [types.types_limit_π], refl },
  map_mul := λ x y, by { simp only [types.types_limit_π], refl },
  map_add := λ x y, by { simp only [types.types_limit_π], refl } }

def limit (F : J ⥤ CommRing.{u}) : cone F :=
{ X := ⟨limit (F ⋙ forget), by apply_instance⟩,
  π :=
  { app := λ j, ⟨limit.π (F ⋙ forget) j, by apply_instance⟩,
    naturality' := λ j j' f, subtype.eq ((limit.cone (F ⋙ forget)).π.naturality f) } }

def limit_is_limit (F : J ⥤ CommRing.{u}) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful forget (limit.is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
  dsimp, split,
  { apply subtype.eq, funext, dsimp,
    erw is_ring_hom.map_one (CommRing.forget.map (s.π.app j)), refl },
  { intros x y, apply subtype.eq, funext, dsimp,
    erw is_ring_hom.map_mul (CommRing.forget.map (s.π.app j)), refl },
  { intros x y, apply subtype.eq, funext, dsimp,
    erw is_ring_hom.map_add (CommRing.forget.map (s.π.app j)), refl },
end

instance CommRing_has_limits : has_limits.{u} CommRing.{u} :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI { cone := limit F, is_limit := limit_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : CommRing.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget)) } }

end CommRing
