import algebraic_geometry.morphisms.finite_type
import algebraic_geometry.GroupObject.better.Grp_
import category_theory.limits.constructions.over.products
import category_theory.limits.full_subcategory
universes v u

open category_theory algebraic_geometry category_theory.limits

variables (k : CommRing)

class finite_type {X Y : Scheme} (f : X ⟶ Y)
  extends locally_of_finite_type f, quasi_compact f : Prop

/-- An algebraic scheme over k is a scheme of finite type over k. -/
@[derive category] def AlgSchemeOver :=
full_subcategory (λ X : over (Scheme.Spec_obj k), finite_type X.hom)

local attribute [instance] over.construct_products.over_binary_product_of_pullback
local attribute [instance] over.over_has_terminal

namespace AlgSchemeOver

instance finite_type_of_binary_product (X Y : AlgSchemeOver k) :
  finite_type (X.1 ⨯ Y.1).hom := sorry

lemma closed_under_binary_products  :
  closed_under_limits_of_shape (discrete walking_pair)
    (λ X : over (Scheme.Spec_obj k), finite_type X.hom) := sorry

instance finite_type_of_terminal :
  finite_type (⊤_ (over (Scheme.Spec_obj k))).hom :=
sorry

lemma closed_under_terminal :
  closed_under_limits_of_shape (discrete.{0} pempty)
    (λ X : over (Scheme.Spec_obj k), finite_type X.hom) :=
sorry

instance : has_terminal (AlgSchemeOver k) := sorry
instance : has_binary_products (AlgSchemeOver k) := sorry
instance : has_finite_products (AlgSchemeOver k) :=
has_finite_products_of_has_binary_and_terminal

end AlgSchemeOver

@[derive category] def GroupAlgSchemeOver := Grp_ (AlgSchemeOver k)

namespace GroupAlgSchemeOver

noncomputable instance : monoidal_category (GroupAlgSchemeOver k) :=
Grp_.Grp_monoidal

end GroupAlgSchemeOver
