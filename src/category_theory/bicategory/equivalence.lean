/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

namespace category_theory

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace bicategory

open_locale bicategory

structure equivalence {B : Type u₁} [bicategory.{w₁ v₁} B] (a b : B) :=
(hom : a ⟶ b)
(inv : b ⟶ a)
(unit_iso : 𝟙 a ≅  hom ≫ inv)
(counit_iso : inv ≫ hom ≅ 𝟙 b)

structure equivalence' {B : Type u₁} [bicategory.{w₁ v₁} B] (a b : B) :=
(hom : a ⟶ b)
(inv : b ⟶ a)
(unit_iso : 𝟙 a ≅  hom ≫ inv)
(counit_iso : inv ≫ hom ≅ 𝟙 b)
(hom_unit_iso_comp' : ∀ a: B,
  (λ_ hom).symm ≪≫ whisker_right_iso unit_iso hom ≪≫ α_ _ _ _
  ≪≫ whisker_left_iso hom counit_iso ≪≫ (ρ_ hom)
  = iso.refl hom . obviously)

variables
{B : Type u₁} [bicategory.{w₁ v₁} B]
{C : Type u₂} [bicategory.{w₁ v₂} C]
{a b : B}
{f : a ⟶ b}
{g : b ⟶ a}
(η : 𝟙 a ≅  f ≫ g)
(ε : g ≫ f ≅ 𝟙 b)

def adjointify_η : 𝟙 a ≅ f ≫ g :=
calc
  𝟙 a ≅ f ≫ g : η
  ... ≅ f ≫ (𝟙 b ≫ g)       : whisker_left_iso f (λ_ g).symm
  ... ≅ f ≫ ((g ≫ f) ≫ g) : whisker_left_iso f (whisker_right_iso ε.symm g)
  ... ≅ f ≫ (g ≫ (f ≫ g)) : whisker_left_iso f (α_ g f g)
  ... ≅ (f ≫ g) ≫ (f ≫ g) : (α_ f g (f ≫ g)).symm
  ... ≅ 𝟙 a ≫ (f ≫ g)       : whisker_right_iso η.symm (f ≫ g)
  ... ≅ f ≫ g                 : λ_ (f ≫ g)

def adjointify_ε : g ≫ f ≅ 𝟙 b :=
calc
  g ≫ f ≅ (g ≫ f) ≫ 𝟙 b       : (ρ_ (g ≫ f)).symm
  ...    ≅ (g ≫ f) ≫ (g ≫ f) : whisker_left_iso (g ≫ f) ε.symm
  ...    ≅ g ≫ (f ≫ (g ≫ f)) : (α_ g f (g ≫ f))
  ...    ≅ g ≫ ((f ≫ g) ≫ f) : whisker_left_iso g (α_ f g f).symm
  ...    ≅ g ≫ (𝟙 a ≫ f)      : whisker_left_iso g (whisker_right_iso η.symm f)
  ...    ≅ g ≫ f                : whisker_left_iso g (λ_ f)
  ...    ≅ 𝟙 b                   : ε

-- example :
--   (λ_ f).symm ≪≫ whisker_right_iso η f ≪≫ α_ _ _ _
--   ≪≫ whisker_left_iso f (adjointify_ε η ε) ≪≫ ρ_ f
--   = iso.refl f :=
-- begin
--   ext, dsimp [adjointify_ε], simp,
--   sorry
-- end

-- lemma adjointify_ε_η :
--     (ρ_ g).symm ≪≫ whisker_left_iso g η ≪≫ (α_ _ _ _).symm
--   ≪≫ whisker_right_iso (adjointify_ε η ε) g ≪≫ (λ_ g)
--   = iso.refl g :=
-- begin
--   sorry
-- end

-- lemma adjointify_η_ε :
--     (λ_ f).symm ≪≫ whisker_right_iso (adjointify_η η ε) f ≪≫ α_ _ _ _
--   ≪≫ whisker_left_iso f ε ≪≫ (ρ_ f)
--   = iso.refl f :=
-- begin
--   sorry
-- end

end bicategory

end category_theory
