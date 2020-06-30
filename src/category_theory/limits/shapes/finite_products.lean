/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_limits

universes v u

open category_theory
namespace category_theory.limits

variables (C : Type u) [category.{v} C]

class has_finite_products :=
(has_limits_of_shape : Π (J : Type v) [fintype J] [decidable_eq J], has_limits_of_shape (discrete J) C)
class has_finite_coproducts :=
(has_colimits_of_shape : Π (J : Type v) [fintype J] [decidable_eq J], has_colimits_of_shape (discrete J) C)

attribute [instance] has_finite_products.has_limits_of_shape has_finite_coproducts.has_colimits_of_shape

@[priority 100] -- see Note [lower instance priority]
instance has_finite_products_of_has_products [has_products C] : has_finite_products C :=
{ has_limits_of_shape := λ J _, by apply_instance }
@[priority 100] -- see Note [lower instance priority]
instance has_finite_coproducts_of_has_coproducts [has_coproducts C] : has_finite_coproducts C :=
{ has_colimits_of_shape := λ J _, by apply_instance }

@[priority 100] -- see Note [lower instance priority]
instance has_finite_products_of_has_finite_limits [has_finite_limits C] : has_finite_products C :=
{ has_limits_of_shape := λ J _ _, by { resetI, apply_instance } }
@[priority 100] -- see Note [lower instance priority]
instance has_finite_coproducts_of_has_finite_colimits [has_finite_colimits C] : has_finite_coproducts C :=
{ has_colimits_of_shape := λ J _ _, by { resetI, apply_instance } }

end category_theory.limits
