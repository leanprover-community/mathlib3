-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits

universes v u

open category_theory
open category_theory.functor

namespace category_theory.limits

variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞
variables {J : Type v} [small_category J]

variables {F : J ⥤ Cᵒᵖ}

def cone_of_cocone_left_op (c : cocone F.left_op) : cone F :=
{ X := op c.X,
  π := nat_trans.right_op (c.ι ≫ (const.op_obj_unop (op c.X)).hom), }

@[simp] lemma cone_of_cocone_left_op_X (c : cocone F.left_op) :
  (cone_of_cocone_left_op c).X = op c.X :=
rfl
@[simp] lemma cone_of_cocone_left_op_π_app (c : cocone F.left_op) (j) :
  (cone_of_cocone_left_op c).π.app j = (c.ι.app (op j)).op :=
begin
  dsimp [cone_of_cocone_left_op],
  simp,
end

def cocone_left_op_of_cone (c : cone F) : cocone (F.left_op) :=
{ X := unop c.X,
  ι := nat_trans.left_op c.π, }

@[simp] lemma cocone_left_op_of_cone_X (c : cone F) :
  (cocone_left_op_of_cone c).X = unop c.X :=
rfl
@[simp] lemma cocone_left_op_of_cone_ι_app (c : cone F) (j) :
  (cocone_left_op_of_cone c).ι.app j = (c.π.app (unop j)).unop :=
begin
  dsimp [cocone_left_op_of_cone],
  simp,
end

def cocone_of_cone_left_op (c : cone F.left_op) : cocone F :=
{ X := op c.X,
  ι := nat_trans.right_op ((const.op_obj_unop (op c.X)).hom ≫ c.π), }

@[simp] lemma cocone_of_cone_left_op_X (c : cone F.left_op) :
  (cocone_of_cone_left_op c).X = op c.X :=
rfl
@[simp] lemma cocone_of_cone_left_op_ι_app (c : cone F.left_op) (j) :
  (cocone_of_cone_left_op c).ι.app j = (c.π.app (op j)).op :=
begin
  dsimp [cocone_of_cone_left_op],
  simp,
end

def cone_left_op_of_cocone (c : cocone F) : cone (F.left_op) :=
{ X := unop c.X,
  π := nat_trans.left_op c.ι, }

@[simp] lemma cone_left_op_of_cocone_X (c : cocone F) :
  (cone_left_op_of_cocone c).X = unop c.X :=
rfl
@[simp] lemma cone_left_op_of_cocone_π_app (c : cocone F) (j) :
  (cone_left_op_of_cocone c).π.app j = (c.ι.app (unop j)).unop :=
begin
  dsimp [cone_left_op_of_cocone],
  simp,
end

instance [has_colimits.{v} C] : has_limits.{v} Cᵒᵖ :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone := cone_of_cocone_left_op (colimit.cocone F.left_op),
      is_limit :=
      { lift := λ s, (colimit.desc F.left_op (cocone_left_op_of_cone s)).op,
        fac' := λ s j,
        begin
          rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, ←op_comp,
              colimit.ι_desc, cocone_left_op_of_cone_ι_app, has_hom.hom.op_unop],
          refl, end,
        uniq' := λ s m w,
        begin
          have u := (colimit.is_colimit F.left_op).uniq (cocone_left_op_of_cone s) (m.unop),
          convert congr_arg (λ f : _ ⟶ _, f.op) (u _), clear u,
          intro j,
          dsimp,
          convert congr_arg (λ f : _ ⟶ _, f.unop) (w (unop j)), clear w,
          dsimp,
          simp,
          refl,
        end } } } }

instance [has_limits.{v} C] : has_colimits.{v} Cᵒᵖ :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F,
    { cocone := cocone_of_cone_left_op (limit.cone F.left_op),
      is_colimit :=
      { desc := λ s, (limit.lift F.left_op (cone_left_op_of_cocone s)).op,
        fac' := λ s j,
        begin
          rw [cocone_of_cone_left_op_ι_app, limit.cone_π, ←op_comp,
              limit.lift_π, cone_left_op_of_cocone_π_app, has_hom.hom.op_unop],
          refl, end,
        uniq' := λ s m w,
        begin
          have u := (limit.is_limit F.left_op).uniq (cone_left_op_of_cocone s) (m.unop),
          convert congr_arg (λ f : _ ⟶ _, f.op) (u _), clear u,
          intro j,
          dsimp,
          convert congr_arg (λ f : _ ⟶ _, f.unop) (w (unop j)), clear w,
          dsimp,
          simp,
          refl,
        end } } } }

end category_theory.limits
