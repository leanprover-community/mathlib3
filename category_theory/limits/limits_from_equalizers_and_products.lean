-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits

open category_theory

namespace category_theory.limits

universes u₁ v₁
variables {C : Type u₁} [category.{u₁ v₁} C]

def limits_from_equalizers_and_products
  [has_products.{u₁ v₁} C] [has_equalizers.{u₁ v₁} C] : has_limits.{u₁ v₁} C :=
{ cone := λ J 𝒥 F,
  begin
    resetI,
    let β_obj := (λ j : J, F j),
    let β_hom := (λ f : (Σ p : J × J, p.1 ⟶ p.2), F f.1.2),
    let pi_obj := limits.pi β_obj,
    let pi_hom := limits.pi β_hom,
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
          dsimp at p,
          simp,
          erw category.id_comp,
          erw category.assoc at p,
          simp at p,
          dsimp at p,
          exact (eq.symm p)
        end } }
  end,
  is_limit := λ J 𝒥 F,
  begin resetI, exact
    { lift := λ c,
        equalizer.lift _ _
          (pi.lift (λ j : J, begin have r := c.π j, dsimp at r, exact r end))
          begin ext1, simp, rw ←category.assoc, simp, end,
      fac' := λ s j, begin dsimp, rw ←category.assoc, simp, end }
  end
}

end category_theory.limits