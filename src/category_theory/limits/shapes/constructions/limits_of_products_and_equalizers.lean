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
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- We hide the "implementation details" inside a namespace
namespace has_limit_of_has_products_of_has_equalizers

/--
Corresponding to any functor `F : J ⥤ C`, we construct a new functor from the walking parallel
pair of morphisms to `C`, given by the diagram
```
         s
∏_j F j ===> Π_{f : j ⟶ j'} F j'
         t
```
where the two morphisms `s` and `t` are defined componentwise:
* The `s_f` component is the projection `∏_j F j ⟶ F j` followed by `f`.
* The `t_f` component is the projection `∏_j F j ⟶ F j'`.

In a moment we prove that cones over `F` are isomorphism to cones over this new diagram.
-/
@[simp] def diagram [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) : walking_parallel_pair ⥤ C :=
let pi_obj := limits.pi_obj F.obj in
let pi_hom := limits.pi_obj (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2) in
let s : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π F.obj f.1.1 ≫ F.map f.2) in
let t : pi_obj ⟶ pi_hom :=
  pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π F.obj f.1.2) in
parallel_pair s t

/-- The morphism from cones over the walking pair diagram `diagram F` to cones over
the original diagram `F`. -/
@[simp] def cones_hom [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (diagram F).cones ⟶ F.cones :=
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

/-- The morphism from cones over the original diagram `F` to cones over the walking pair diagram
`diagram F`. -/
@[simp] def cones_inv [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  F.cones ⟶ (diagram F).cones :=
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

/-- The natural isomorphism between cones over the
walking pair diagram `equalizer_diagram F` and cones over the original diagram `F`. -/
def cones_iso [has_products.{v} C] {J} [small_category J] (F : J ⥤ C) :
  (diagram F).cones ≅ F.cones :=
{ hom := cones_hom F,
  inv := cones_inv F,
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

end has_limit_of_has_products_of_has_equalizers

open has_limit_of_has_products_of_has_equalizers

instance has_limit_of_has_products_of_has_equalizers
  [has_products.{v} C] [has_equalizers.{v} C] {J} [small_category J] (F : J ⥤ C) :
    has_limit.{v} F :=
has_limit.of_cones_iso (diagram F) F (cones_iso F)

/-- Any category with products and equalizers has all limits. -/
-- This is not an instance, as it is not always how one wants to construct limits!
def limits_from_equalizers_and_products
  [has_products.{v} C] [has_equalizers.{v} C] : has_limits.{v} C :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, by apply_instance } }

end category_theory.limits
