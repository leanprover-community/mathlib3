import category_theory.concrete_category.bundled_hom
import category_theory.concrete_category.basic
import category_theory.monoidal.functorial
import category_theory.monoidal.types

open category_theory

universes v u

class enriched_over
  (C : Type u) [category.{v} C]
  (V : Type v → Type v)
  {hom : Π ⦃α β : Type v⦄ (Iα : V α) (Iβ : V β), Type v} [bundled_hom hom]
  [monoidal_category (bundled V)] [lax_monoidal (forget (bundled V)).obj] :=
(ehom : Π X Y : C, V (X ⟶ Y))
(eid : Π X, 𝟙_ (bundled V) ⟶ @bundled.of V (X ⟶ X) (ehom X X))
(ecomp : Π X Y Z,
  (@bundled.of V (X ⟶ Y) (ehom X Y) ⊗ @bundled.of V (Y ⟶ Z) (ehom Y Z)) ⟶
    @bundled.of V (X ⟶ Z) (ehom X Z))
(eid_forget : ∀ (X : C),
  (forget (bundled V)).map (eid X)
    (lax_monoidal.ε_type (forget (bundled V)).obj) = 𝟙 X)
(ecomp_forget : ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
  (forget (bundled V)).map (ecomp X Y Z) (lax_monoidal.μ_type (forget (bundled V)).obj f g) = f ≫ g)
