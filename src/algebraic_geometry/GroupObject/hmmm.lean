import algebraic_geometry.pullbacks
import category_theory.limits.constructions.over.products
import category_theory.monoidal.of_has_finite_products
import algebraic_geometry.GroupObject.over_Affine_Spec_equivalence
universes v u
noncomputable theory
open category_theory algebraic_geometry category_theory.limits opposite

variables (R : CommRing)

local attribute [instance] over.over_has_terminal
  over.construct_products.over_binary_product_of_pullback

--abbreviation overR := over (Scheme.Spec_obj R)
--instance : has_finite_products (overR R) := has_finite_products_of_has_binary_and_terminal
--noncomputable instance : monoidal_category (overR R) := monoidal_of_has_finite_products _
#exit
abbreviation Affine_over := over (AffineScheme.Spec.obj $ op R)
instance : has_finite_products (Affine_over R) := has_finite_products_of_has_binary_and_terminal
instance : monoidal_category (Affine_over R) := monoidal_of_has_finite_products _
instance : monoidal_category (CommAlg R) := by apply_instance
def over_Spec := (CommAlg.over_Affine_Spec_equivalence R).functor
def monoidal_Spec : monoidal_functor
