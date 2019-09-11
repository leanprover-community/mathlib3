/-
-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/

import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.equalizers

/-!
# Constructing finite limits from finite products and equalizers.

If a category has all finite products, and all equalizers, then it has all finite limits.

## Implementation note
This is exactly the same proof that all products and all equalizers provide all limits, from
`constructions/limits_of_products_and_equalizers`, except with more restrictive hypotheses.

TODO: provide the dual result.
-/

open category_theory
open opposite

namespace category_theory.limits

universes v u
variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

-- Finding the `decidable_eq` instances apparent takes some work.
set_option class.instance_max_depth 38

variables {J : Type v} [small_category J] [𝒥 : fin_category J]
include 𝒥

@[simp] def fin_equalizer_diagram [has_finite_products.{v} C] (F : J ⥤ C) : walking_parallel_pair ⥤ C :=
let pi_obj := limits.pi_obj F.obj in
let pi_hom := limits.pi_obj (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2) in
let s : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π F.obj f.1.1 ≫ F.map f.2) in
let t : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π F.obj f.1.2) in
parallel_pair s t

@[simp] def fin_equalizer_diagram.cones_hom [has_finite_products.{v} C] (F : J ⥤ C) :
  (fin_equalizer_diagram F).cones ⟶ F.cones :=
{ app := λ X c,
  { app := λ j, c.app walking_parallel_pair.zero ≫ pi.π _ j,
    naturality' := λ j j' f,
    begin
      have L := c.naturality walking_parallel_pair_hom.left,
      have R := c.naturality walking_parallel_pair_hom.right,
      have t := congr_arg (λ g, g ≫ pi.π _ (⟨(j, j'), f⟩ : Σ (p : J × J), p.fst ⟶ p.snd)) (R.symm.trans L),
      dsimp at t,
      dsimp,
      simpa only [limit.lift_π, fan.mk_π_app, category.assoc, category.id_comp] using t,
    end }, }.

@[simp] def fin_equalizer_diagram.cones_inv [has_finite_products.{v} C] (F : J ⥤ C) :
  F.cones ⟶ (fin_equalizer_diagram F).cones :=
{ app := λ X c,
  begin
    refine (fork.of_ι _ _).π,
    { exact pi.lift c.app },
    { ext f,
      rcases f with ⟨⟨A,B⟩,f⟩,
      dsimp,
      simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
      rw ←(c.naturality f),
      dsimp,
      simp only [category.id_comp], }
  end,
  naturality' := λ X Y f, by { ext c j, cases j; tidy, } }.

def fin_equalizer_diagram.cones_iso [has_finite_products.{v} C] (F : J ⥤ C) :
  (fin_equalizer_diagram F).cones ≅ F.cones :=
{ hom := fin_equalizer_diagram.cones_hom F,
  inv := fin_equalizer_diagram.cones_inv F,
  hom_inv_id' :=
  begin
    ext X c j,
    cases j,
    { ext, simp },
    { ext,
      have t := c.naturality walking_parallel_pair_hom.left,
      conv at t { dsimp, to_lhs, simp only [category.id_comp] },
      simp [t], }
  end }

instance has_limit_of_has_finite_products_of_has_equalizers [has_finite_products.{v} C] [has_equalizers.{v} C] (F : J ⥤ C) :
  has_limit.{v} F :=
has_limit.of_cones_iso (fin_equalizer_diagram F) F (fin_equalizer_diagram.cones_iso F)

omit 𝒥

def finite_limits_from_equalizers_and_finite_products
  [has_finite_products.{v} C] [has_equalizers.{v} C] : has_finite_limits.{v} C :=
{ has_limits_of_shape := λ J _ _, by exactI
  { has_limit := λ F, by apply_instance } }

end category_theory.limits
