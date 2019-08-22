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

namespace category_theory.limits

universes v u
variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

-- This should be easy: a limit of F is exactly on object representing F.cones.
def has_limit.of_cones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cones ≅ G.cones) [has_limit F] : has_limit G := sorry
-- { cone :=
--   let t := ((cone.equiv F).hom (limit.cone F)) in
--   (cone.equiv G).inv ⟨_, (h.hom.app t.1 t.2)⟩,
--   is_limit :=
--   begin
--     apply is_limit.of_nat_iso,
--     transitivity,
--     swap,
--     exact h,
--     dsimp,
--     transitivity,
--     swap,
--     apply is_limit.nat_iso (limit.is_limit F),
--     apply nat_iso.of_components,
--     swap,
--     intros,
--     dsimp,

--   end }

def equalizer_diagram [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) : walking_parallel_pair ⥤ C :=
let β_obj := (λ j : J, F.obj j) in
let β_hom := (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2) in
let pi_obj := limits.pi_obj β_obj in
let pi_hom := limits.pi_obj β_hom in
let s : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.1 ≫ F.map f.2) in
let t : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.2) in
parallel_pair s t

def equalizer_diagram.cones_iso [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (equalizer_diagram F).cones ≅ F.cones :=
{ hom :=
  { app := λ X c,
    { app := λ j, c.app walking_parallel_pair.zero ≫ pi.π _ j,
      naturality' := λ j j' f, sorry }, },
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

instance [has_products.{v} C] [has_equalizers.{v} C] {J} [small_category J] (F : J ⥤ C) :
  has_limit.{v} F :=
has_limit.of_cones_iso (equalizer_diagram F) F (equalizer_diagram.cones_iso F)

def limits_from_equalizers_and_products
  [has_products.{v} C] [has_equalizers.{v} C] : has_limits.{v} C :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, by apply_instance } }

end category_theory.limits
