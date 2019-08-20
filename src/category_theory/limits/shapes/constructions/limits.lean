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

def limits_from_equalizers_and_products
  [has_products.{v} C] [has_equalizers.{v} C] : has_limits.{v} C :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
{ cone :=
  begin
    let β_obj := (λ j : J, F.obj j),
    let β_hom := (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2),
    let pi_obj := limits.pi_obj β_obj,
    let pi_hom := limits.pi_obj β_hom,
    let s : pi_obj ⟶ pi_hom :=
      pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.1 ≫ F.map f.2),
    let t : pi_obj ⟶ pi_hom :=
      pi.lift (λ f : (Σ p : J × J, p.1 ⟶ p.2), pi.π β_obj f.1.2),
    exact
    { X := equalizer s t,
      π :=
      { app := λ j, equalizer.ι s t ≫ pi.π β_obj j,
        naturality' := λ j j' f,
        begin
          rw category.assoc,
          have p := congr_arg (λ φ, φ ≫ pi.π β_hom ⟨ ⟨ j, j' ⟩, f ⟩) (equalizer.w s t),
          -- TODO cleanup
          dsimp at p,
          simp,
          erw category.id_comp,
          erw category.assoc at p,
          simp at p,
          exact (eq.symm p)
        end } }
  end,
  is_limit :=
  { lift := λ c,
        equalizer.lift _ _
          (pi.lift (λ j : J, begin have r := c.π.app j, dsimp at r, exact r end))
          (begin ext1, dsimp, simp, end),
      uniq' := begin tidy, end }
} } }

end category_theory.limits
