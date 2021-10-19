/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functor
import category_theory.functorial

/-!
# Unbundled lax monoidal functors

## Design considerations
The essential problem I've encountered that requires unbundled functors is
having an existing (non-monoidal) functor `F : C ⥤ D` between monoidal categories,
and wanting to assert that it has an extension to a lax monoidal functor.

The two options seem to be
1. Construct a separate `F' : lax_monoidal_functor C D`,
   and assert `F'.to_functor ≅ F`.
2. Introduce unbundled functors and unbundled lax monoidal functors,
   and construct `lax_monoidal F.obj`, then construct `F' := lax_monoidal_functor.of F.obj`.

Both have costs, but as for option 2. the cost is in library design,
while in option 1. the cost is users having to carry around additional isomorphisms forever,
I wanted to introduce unbundled functors.

TODO:
later, we may want to do this for strong monoidal functors as well,
but the immediate application, for enriched categories, only requires this notion.
-/

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

open monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
          {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

/-- An unbundled description of lax monoidal functors. -/
-- Perhaps in the future we'll redefine `lax_monoidal_functor` in terms of this,
-- but that isn't the immediate plan.
class lax_monoidal (F : C → D) [functorial.{v₁ v₂} F] :=
-- unit morphism
(ε              [] : 𝟙_ D ⟶ F (𝟙_ C))
-- tensorator
(μ              []  : Π X Y : C, (F X) ⊗ (F Y) ⟶ F (X ⊗ Y))
(μ_natural'       : ∀ {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  ((map F f) ⊗ (map F g)) ≫ μ Y Y' = μ X X' ≫ map F (f ⊗ g)
  . obviously)
-- associativity of the tensorator
(associativity'   : ∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙 (F Z)) ≫ μ (X ⊗ Y) Z ≫ map F (α_ X Y Z).hom
  = (α_ (F X) (F Y) (F Z)).hom ≫ (𝟙 (F X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (λ_ (F X)).hom
  = (ε ⊗ 𝟙 (F X)) ≫ μ (𝟙_ C) X ≫ map F (λ_ X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (ρ_ (F X)).hom
  = (𝟙 (F X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map F (ρ_ X).hom
  . obviously)

restate_axiom lax_monoidal.μ_natural'
attribute [simp] lax_monoidal.μ_natural

restate_axiom lax_monoidal.left_unitality'
restate_axiom lax_monoidal.right_unitality'
-- The unitality axioms cannot be used as simp lemmas because they require
-- higher-order matching to figure out the `F` and `X` from `F X`.

restate_axiom lax_monoidal.associativity'
attribute [simp] lax_monoidal.associativity

namespace lax_monoidal_functor

/--
Construct a bundled `lax_monoidal_functor` from the object level function
and `functorial` and `lax_monoidal` typeclasses.
-/
@[simps]
def of (F : C → D) [I₁ : functorial.{v₁ v₂} F] [I₂ : lax_monoidal.{v₁ v₂} F] :
  lax_monoidal_functor.{v₁ v₂} C D :=
{ obj := F,
  ..I₁, ..I₂ }

end lax_monoidal_functor

instance (F : lax_monoidal_functor.{v₁ v₂} C D) : lax_monoidal.{v₁ v₂} (F.obj) := { .. F }

section

instance lax_monoidal_id : lax_monoidal.{v₁ v₁} (id : C → C) :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _ }

end

-- TODO instances for composition, as required

-- TODO `strong_monoidal`, as well as `lax_monoidal`

end category_theory
