import category_theory.monoidal.natural_transformation
import category_theory.equivalence

open category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open category_theory.equivalence
open category_theory.monoidal_category

namespace category_theory

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁} C]
          {D : Type u₂} [𝒟 : monoidal_category.{v₂} D]
variables (F : monoidal_functor.{v₁ v₂} C D)

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

-- TODO oof, this looks really bad, I want rewrite_search!
def monoidal_inverse [is_equivalence F.to_functor] : monoidal_functor.{v₂ v₁} D C :=
{ ε :=
  begin
    dsimp,
    refine (is_equivalence.unit_iso F.to_functor).hom.app (𝟙_ C) ≫ _,
    dsimp,
    apply F.to_functor.inv.map,
    exact (inv F.ε)
  end,
  ε_is_iso := by { dsimp, apply_instance, }, -- TODO tidy should do this; defer ext
  μ := λ X Y,
  begin
    dsimp,
    refine (is_equivalence.unit_iso F.to_functor).hom.app _ ≫ _,
    dsimp,
    apply F.to_functor.inv.map,
    refine (inv (F.μ _ _) ≫ _),
    refine (is_equivalence.counit_iso _).hom.app _ ⊗ (is_equivalence.counit_iso _).hom.app _,
  end,
  μ_is_iso := λ X Y, by { dsimp, apply is_iso.comp_is_iso, }, -- why can't apply_instance solve this?
  μ_natural' := λ X Y X' Y' f g, begin dsimp, sorry, end,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ..(F.to_functor.inv) }

end category_theory
