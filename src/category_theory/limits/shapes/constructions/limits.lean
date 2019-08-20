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
          dsimp,
          simp only [category.id_comp, category.assoc],
          have p := congr_arg (λ φ, φ ≫ pi.π β_hom ⟨ ⟨ j, j' ⟩, f ⟩) (equalizer.w s t).symm,
          dsimp at p,
          simp only [limit.lift_π, fan.mk_π_app, category.assoc] at p,
          exact p
        end } }
  end,
  is_limit :=
  { lift := λ c, equalizer.lift _ _
      (pi.lift (λ j : J, begin have r := c.π.app j, dsimp at r, exact r end))
      (begin ext1, dsimp, simp, end),
    uniq' := λ s m w,
    begin
      dsimp at *,
      ext1 z, cases z,
      { ext1 j, simp, rw ←(w j), },
      { ext1 j, simp, rw ←(w j.1.2), dsimp,
        erw ←(limit.w (parallel_pair _ _) walking_parallel_pair_hom.left),
        rw category.assoc,
        dsimp,
        simp,
        sorry } end }
} } }

end category_theory.limits
