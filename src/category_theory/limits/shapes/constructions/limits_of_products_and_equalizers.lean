/-
-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/

import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.

TODO: provide the dual result.
-/

open category_theory
open opposite

namespace category_theory.limits

universes v u
variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

def has_limit.of_cones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cones ≅ G.cones) [has_limit F] : has_limit G :=
⟨_, is_limit.of_nat_iso ((is_limit.nat_iso (limit.is_limit F)) ≪≫ h)⟩

def equalizer_diagram [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) : walking_parallel_pair ⥤ C :=
-- TODO: probably can inline some of these lets
let β_obj := (λ j : J, F.obj j) in
let β_hom := (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2) in
let pi_obj := limits.pi_obj β_obj in
let pi_hom := limits.pi_obj β_hom in
let s : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.1 ≫ F.map f.2) in
let t : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.2) in
parallel_pair s t

@[simp] lemma equalizer_diagram_map_left [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (equalizer_diagram F).map walking_parallel_pair_hom.left = pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π (λ j : J, F.obj j) f.1.1 ≫ F.map f.2) :=
rfl
@[simp] lemma equalizer_diagram_map_right [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (equalizer_diagram F).map walking_parallel_pair_hom.right = pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π (λ j : J, F.obj j) f.1.2) :=
rfl

@[simp] def equalizer_diagram.cones_hom [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (equalizer_diagram F).cones ⟶ F.cones :=
{ app := λ X c,
  { app := λ j, c.app walking_parallel_pair.zero ≫ pi.π _ j,
    naturality' := λ j j' f,
    begin
      have L := c.naturality walking_parallel_pair_hom.left,
      have R := c.naturality walking_parallel_pair_hom.right,
      have t := congr_arg (λ g, g ≫ pi.π _ (⟨(j, j'), f⟩ : Σ (p : J × J), p.fst ⟶ p.snd)) (R.symm.trans L),
      simp only [limit.lift_π, equalizer_diagram_map_right, fan.mk_π_app, equalizer_diagram_map_left, category.assoc] at t,
      dsimp,
      simp only [category.id_comp, category.assoc],
      exact t
    end }, }.

@[simp] def equalizer_diagram.cones_inv [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  F.cones ⟶ (equalizer_diagram F).cones :=
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
  naturality' :=
  begin
    -- TODO cleanup. why are the erw's needed?
    tidy,
    cases X_1; tidy,
    { erw functor.cones_map_app, simp, },
    { erw functor.cones_map_app, simp, },
  end }.

def equalizer_diagram.cones_iso [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (equalizer_diagram F).cones ≅ F.cones :=
{ hom := equalizer_diagram.cones_hom F,
  inv := equalizer_diagram.cones_inv F,
  hom_inv_id' :=
  begin
    ext X c j,
    cases j,
    { ext, simp },
    { ext,
      have t := c.naturality walking_parallel_pair_hom.left,
      conv at t { to_lhs, dsimp, simp only [category.id_comp] },
      simp [t], }
  end }

instance [has_products.{v} C] [has_equalizers.{v} C] {J} [small_category J] (F : J ⥤ C) :
  has_limit.{v} F :=
has_limit.of_cones_iso (equalizer_diagram F) F (equalizer_diagram.cones_iso F)

def limits_from_equalizers_and_products
  [has_products.{v} C] [has_equalizers.{v} C] : has_limits.{v} C :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, by apply_instance } }

end category_theory.limits
