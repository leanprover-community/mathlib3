import algebra.category.Mon.limits
import category_theory.limits.shapes.finite_products
import category_theory.monoidal.of_has_finite_products

open category_theory
open tactic

universes u

namespace category_theory.monoidal

local attribute [instance] monoidal_of_has_finite_products

/- Cartesian monoidal structure on Mon -/
instance mon_monoidal : monoidal_category Mon := monoidal_of_has_finite_products Mon

/- @[simp] lemma tensor_apply {W X Y Z : Mon} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
(f ⊗ g) p = (f p.1, g p.2) := rfl

@[simp] lemma left_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((λ_ X).hom : (𝟙_ (Mon)) ⊗ X → X) (p, x) = x := rfl
@[simp] lemma left_unitor_inv_apply {X : Mon} {x : X} :
  ((λ_ X).inv : X ⟶ (𝟙_ (Mon)) ⊗ X) x = (punit.star, x) := rfl

@[simp] lemma right_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((ρ_ X).hom : X ⊗ (𝟙_ (Mon)) → X) (x, p) = x := rfl
@[simp] lemma right_unitor_inv_apply {X : Mon} {x : X} :
  ((ρ_ X).inv : X ⟶ X ⊗ (𝟙_ (Mon))) x = (x, punit.star) := rfl

@[simp] lemma associator_hom_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)) ((x, y), z) = (x, (y, z)) := rfl
@[simp] lemma associator_inv_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).inv : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) := rfl -/

end category_theory.monoidal
